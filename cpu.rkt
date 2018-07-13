#lang racket
(require (for-syntax syntax/parse racket/syntax racket/format racket/base)
         racket/draw)
(provide
 ;; Emulation
 run       ; run until STOP 
 continue  ; continue from STOP
 step      ; single step
 ;; Memory
 load load2 store mem-dump
 ;; Registers
 A X Y PC S C Z V 
 ;; Assembler
 assembler traditional->assembler assembler->traditional
 install-opcodes-from-assembler
 ;; Other
 split-string-into-lines hex hex$ bin bin%)

;;;
;;; References
;;;

;;; Opcode reference:
;;;     http://www.6502.org/tutorials/6502opcodes.html#SBC
;;; Opcode reference and pseudo code from Vice:
;;;     http://nesdev.com/6502.txt

;;;
;;; SETTINGS
;;;

(define video-type 'pal)

;;;
;;; TODO
;;;

; - implement sbc
; Extend tradional->assembler to handle comments

; The +1 extra cycle for page boundary crossings needs to be handled.
; Finish the assembler. I.e. support labels and symbols.
; Tests ...
; Load files from other assemblers
; Load and save rom files.
; Memory banks

; Support the unsupported opcodes:
;   ALR: A:=(A and #{imm})/2;
;   ANC: A:=A and #{imm}; Generates opcode $0B.
;   ARR: A:=(A and #{imm})/2;
;   AXS: X:=A and X-#{imm};
;   DCP: {adr}:={adr}-1; A-{adr};
;   ISC: {adr}:={adr}+1; A:=A-{adr};
;   LAS: A,X,S:={adr} and S;
;   LAX: A,X:={adr};
;   RLA: {adr}:={adr}rol; A:=A and {adr};
;   RRA: {adr}:={adr}ror; A:=A adc {adr};
;   SAX: {adr}:=A and X;
;   SLO: {adr}:={adr}*2; A:=A or {adr};
;   SRE: {adr}:={adr}/2; A:=A xor {adr};

;;;
;;; SYNTAX UTILITIES
;;;

(module utils racket
  (provide symbol-downcase symbol-upcase syntax-downcase syntax-upcase)
  (define (convert s f)
    (if (syntax? s)
        (convert (syntax-e s) f)
        (string->symbol (f (symbol->string s)))))
  (define (symbol-downcase s) (convert s string-downcase))
  (define (symbol-upcase s)   (convert s string-upcase))
  (define (syntax-downcase ctx stx-sym)
    (datum->syntax ctx (symbol-downcase (syntax-e stx-sym))))
  (define (syntax-upcase ctx stx-sym)
    (datum->syntax ctx (symbol-upcase (syntax-e stx-sym)))))

(require (submod "." utils))

(begin-for-syntax
  (require (submod "." utils))
  (define (format-ids locs fmt vss)
    (for/list ([vs  (syntax->list vss)] [loc (syntax->list locs)])
      (apply format-id loc fmt (syntax->list vs)))))

;;;
;;; BITS AND BYTES
;;;

(define bitand  bitwise-and)
(define bitor   bitwise-ior)
(define bitxor  bitwise-xor)

(define (bitasl n)            (arithmetic-shift n  1))
(define (bitlsr n)            (arithmetic-shift n -1)) ; introduces 0 as msb
(define byte-masks            #(1 2 4 8 16 32 64 128))
(define negated-byte-masks    (for/vector ([b byte-masks]) (- 255 b)))
(define (bit-clear? b pos)         (zero? (bitand b (vector-ref byte-masks pos))))
(define (bit-set?   b pos)    (not (zero? (bitand b (vector-ref byte-masks pos)))))
(define (bit-clear  b pos)    (bitand b (vector-ref negated-byte-masks pos)))
(define (bit-set    b pos)    (bitor  b (vector-ref         byte-masks pos)))
(define (low bits)            (bitwise-and bits #xff))    ; returns the low  8 bits
(define (high bits)           (arithmetic-shift bits -8)) ; returns the high 8 bits
(define (bit-ref bits pos)    (byte>> (bitwise-and bits (vector-ref byte-masks pos)) pos))

(define (byte-msb? b)         (not (zero? (bitand b #b10000000))))
(define (byte-set-msb b)      (bitor  b #b10000000))
(define (byte-clear-msb b)    (bitand b #b01111111))
(define (byte-set-lsb b)      (bitor  b #b00000001))
(define (byte-clear-lsb b)    (bitand b #b11111110))
(define (byte-inc b)          (if (= b 255)   0 (+ b 1)))
(define (byte-dec b)          (if (= b 0)   255 (- b 1)))
(define (byte-pos? b)         (not (byte-msb? b)))
(define (byte-neg? b)              (byte-msb? b))
(define (byte-neg b)          (byte (bitxor b #xff))) ; negation
(define (byte-zero? b)        (= b 0))
(define (byte-one? b)         (= b 1))
(define (byte n)              (bitand             n #xFF))

(define (byte+ b c)           (bitand (+ b c)       #xFF))
(define (byte- b c)           (bitand (- b c)       #xFF)) ; todo check this!
(define (byte-or b c)         (bitand (bitor   b c) #xFF))
(define (byte-xor b c)        (bitand (bitxor  b c) #xFF))
(define (byte-and b c)        (bitand (bitand b c)  #xFF))
(define (byte-asl b)          (bitand (bitasl b)    #xFF))
(define (byte-lsr b)          (bitand (bitlsr b)    #xFF))
(define (byte-rol b c?)       (if c? (byte-set-lsb (byte-asl b)) (byte-asl b)))
(define (byte-ror b c?)       (if c? (byte-set-msb (byte-lsr b)) (byte-lsr b)))
(define (byte<< b n)          (arithmetic-shift b n))
(define (byte>> b n)          (arithmetic-shift b (- n)))
(define (byte-lower-nibble b) (bitand b #b00001111))
(define (byte-upper-nibble b) (arithmetic-shift b -4))
(define (nibbles->byte u l)   (byte-or (arithmetic-shift u 4) l))

(define (word hi lo)    (+ (* hi 256) lo))
(define (word+ w1 w2)   (bitand (+ w1 w2) #xFFFF))
(define (word- w1 w2)   (bitand (- w1 w2) #xFFFF))
(define (word>> w n)    (arithmetic-shift w (- n)))
(define (word-and b c)  (bitand (bitand b c) #xFFFF))
(define (word-msb w)    (word>> w 8))
(define (word-lsb w)    (word-and w #xFF))

(define (hex2 n)  (~r n #:base 16 #:min-width 2 #:pad-string "0"))
(define (hex4 n)  (~r n #:base 16 #:min-width 4 #:pad-string "0"))
(define hex hex2)
(define (hex$ n)  (string->symbol (string-append "$" (if (<= n #xff) (hex2 n) (hex4 n)))))
(define (bin8 n)  (~r n #:base 2 #:min-width  8 #:pad-string "0"))
(define (bin16 n) (~r n #:base 2 #:min-width 16 #:pad-string "0"))
(define bin bin8)
(define (bin% n)  (string->symbol (string-append "%" (if (<= n #xff) (bin8 n) (bin16 n)))))

;;;
;;; REGISTERS
;;;

(define-syntax (define-register stx)
  (syntax-parse stx
    [(_define-register name)
     (with-syntax ([name! (format-id #'name "~a!" #'name)])
       #'(begin (define name 0)
                (define-syntax (name! so)
                  (syntax-parse so [(_name! expr) (syntax/loc so (set! name expr))]))))]))

(define-register A)   ; accumulator      ( 8 bit)
(define-register X)   ; index register   ( 8 bit)
(define-register Y)   ; index register   ( 8 bit)
(define-register SP)  ; stack pointer    ( 8 bit)
(define-register PC)  ; program counter  (16 bit)

(define (~registers)
  (~a "A:"  (hex2 A) " "
      "X:"  (hex2 X) " "
      "Y:"  (hex2 Y) " "
      "SP:" (hex2 SP)))

;;;
;;; STATUS REGISTER: FLAGS
;;; 

; The status register contains 8 flags.
; The status register is represented as 8 individual flags.

(define-syntax (define-flags stx)
  (syntax-parse stx
    [(_define-flags (name bit-number description) ...)
     (with-syntax ([(name! ...) (format-ids #'(name ...) "~a!" #'((name) ...))])
       #'(begin (define name 0) ...
                (define (name! v) (set! name v)) ...))]))

(define-flags
  (C 0 carry)          ; contains the result affecting the flag (set if result<#0x100 )
  (Z 1 zero)           ; contains the last byte affecting the flag
  (I 2 interrupt)      ; boolean
  (D 3 decimal-mode)   ; boolean
  (B 4 break)          ; boolean
  (U 5 unused)         ; #t
  (V 6 overflow)       ; 0 or 1
  (S 7 sign))          ; contains the last byte affecting the flag

(define (reset-status-register)
  (C! #x100) (Z! 0) (I! #f) (D! #t) (B! #f) (U! #t) (V! 0) (S! 0))

; Note: The sign flag is also known as the N flag (for Negative)
(define (S?)      (byte-neg? S))   ; true, if the (negative) sign is set
(define (set-S)   (S! #b10000000))
(define (clear-S) (S! 0))

(define (Z?)      (zero? Z))       ; true, if the zero  flag is set
(define (set-Z)   (Z! 0))
(define (clear-Z) (Z! 1))

(define (V?)      (= V 1))         ; true, if overflow is set
(define (set-V)   (V! 1))
(define (clear-V) (V! 0))

(define (C?)      (< C #x100))     ; true, if the carry flag is set
(define (set-C)   (C! 0))
(define (clear-C) (C! #x100))

(define (I?)      I)
(define (set-I)   (I! #t))
(define (clear-I) (I! #f))

(define (B?)      B)
(define (set-B)   (B! #t))
(define (clear-B) (B! #f))

(define (D?)      D)
(define (set-D)   (D! #t))  
(define (clear-D) #;(D! #f) (void))  ; The 6502 in the NES doesn't support the decimal flag
;                                    ; so .. make this void

(define (~flags)
  (~a (if (C?) "C" ".")
      (if (Z?) "Z" ".")
      (if I    "I" ".")
      (if D    "D" ".")
      (if B    "B" ".")
      (if U    "_" "_")
      (if (V?) "V" ".")
      (if (S?) "S" ".")))

(define (flags->integer)
  (string->number
   (string-append*
    (reverse
     (list (if (C?) "1" "0")
           (if (Z?) "1" "0")
           (if I    "1" "0")
           (if D    "1" "0")
           (if B    "1" "0")
           (if U    "1" "0")
           (if (V?) "1" "0")
           (if (S?) "1" "0"))))
   2))

;;;
;;; CLOCK
;;;

(define cycle-count 0)

;;;
;;; MEMORY
;;;

;; SIMPLEST MODEL: Simple 64KB address space. No memory mapped IO-registers.
;; The memory is represented as a mutable array of bytes.

; (define mem (make-bytes #x10000 0))
; (define (load a)     (bytes-ref  mem a))
; (define (store a v)  (bytes-set! mem a v))

;;; MEMORY MAPPER 

; Due to the memory mapping of the NES all loads and stores to the memory
; will go through the  load  and  store  below. 

; The smallest ram chips used in the NES (and/or cartridges) are 2KB,
; so let's call a 2KB sized piece of memory a page.

(define (page) (make-vector #x800 0))

; Besides standard ram a few addresses are memory mapped.
; The PPU (graphics chip) have 8 registers that are accessed throgh
; addresses $2000-$2007.

; For now, let's represent the PPU registers as a vector.
(define ppu-registers  (make-vector 8 0))
; We can change the representation later, if all access to the PPU goes through  ppu-ref and ppu-set!
(define (ppu-reg-ref i)    (vector-ref  ppu-registers i))
(define (ppu-reg-set! i b)
  (case i
    [(7)   (ppu-data-write  b)]  ; $2007  ; fast path
    [(0)   ;(displayln (list 'ppu-ctrl (bin b)) (current-error-port))
           (vector-set! ppu-registers i b)]  ; $2000
    [(3)   ;(displayln (list 'ppu-oam-addr (bin b)) (current-error-port))
           (vector-set! ppu-registers i b)]
    [(4)   ;(displayln (list 'ppu-oam-data (bin b)) (current-error-port))
           (vector-set! ppu-registers i b)]
    ; [(1)   (ppu-mask-set!   b)]  ; $2001
    ; [(2)   (ppu-status-set! b)]  ; $2002
    ; [(3)   (ppu-oam-addr! b)]    ; $2003
    ; [(4)   (ppu-oam-data! b)]    ; $2004
    ; [(5)   (ppu-scroll-set! b)]  ; $2005
    [(6)   (ppu-addr-write  b)]    ; $2006    
    [else  (vector-set! ppu-registers i b)]))

; The actual memory layout depends on which chips are present in the cartridge.
; However there are 2KB internal ram (i.e. not on a cartridge) at the beginning
; of the address space. Further more page 2, 3, and, 4 are mirrors of that first page.

; The first page is internal ram. 
; The following pages are mirrors of the first page.
(define page0 (page))  ; $0000 - $0800
(define page1 page0)   ; $0800 - $0FFF  2KB mirror of $0-$7FF
(define page2 page0)   ; $1000 - $17FF  2KB mirror of $0-$7FF
(define page3 page0)   ; $1800 - $1FFF  2KB mirror of $0-$7FF

(define memmap
  (vector page0  page1  page2  page3    ; $0000 - $1FFF 
          #f     #f     #f     #f       ; $2000 - $3FFF  PPU
          #f     (page) (page) (page)   ; $4000 - $5FFF  APU + IO + more
          (page) (page) (page) (page)   ; $6000 - $7FFF

          (page) (page) (page) (page)   ; $8000 - $9FFF
          (page) (page) (page) (page)   ; $A000 - $BFFF
          (page) (page) (page) (page)   ; $C000 - $DFFF
          (page) (page) (page) (page))) ; $E000 - $FFFF

(define (make-$C000-$FFFF-a-mirror-of-$8000-BFFF)
  ; If the prg rom is only 16KB then it needs to be mirrored.
  (for ([i (in-range 8)])
    (vector-set! memmap (+ 24 i) (vector-ref memmap (+ 16 i)))))


(define (load a) ; retrieve the byte value stored at address a
  (define bank     (word>> a 11))                          ; upper 5 bits = the bank number
  (define page     (vector-ref memmap bank))               ; the memmap maps bank to page
  (cond
    [page          (vector-ref page (word-and a #b11111111111))] ; index = lower 11 bits
    [(<= 4 bank 7) (ppu-reg-ref     (word-and a #b111))]   ; index of PPU register = lower 3 bits
    [(= bank 8)    (cond
                     [(= a #x4017) 1]     ; JOY 1 ; XXX TODO
                     [else         0])]   ; we will ignore the APU for the time being
    [else          (error 'load "unexpected ")]))          ; no other banks need special treatment

(define (store a b) ; store the byte value b at address a
  (define bank     (word>> a 11))
  (define page     (vector-ref memmap bank))
  (cond
    [page          (vector-set! page (word-and #b11111111111 a) b)]
    [(<= 4 bank 7) (ppu-reg-set! (word-and a #b111) b)]
    [(= bank 8)    (void)]
    [else          (error 'store "unexpected ")]))

(define (load2 a)    (word (load                    (+ a 1))  (load a)))
(define (load2bug a) (word (load (word (high a) (byte+ a 1))) (load a)))
(define (push! v)    (store (+ #x100 SP) v) (SP! (byte- SP 1)))
(define (pull!)      (SP! (byte+ SP 1))     (load (+ #x100 SP)))
(define (on-zero-page? adr) (< adr 256))

;;;
;;; PPU - Picture Processing Unit
;;;

; The PPU is the graphics chip. It is a small CPU that runs in parallel with the main CPU.
; The PPU has a 16KB ram chip. This ram is refered to as video ram.
; The address space of the PPU is 

; A ppu page is 256 bytes.
(define ppu-page-size 256)
(define (ppu-page)   (make-vector ppu-page-size 0))

(define ppu-memmap   (make-vector (/ (* 64 1024) ppu-page-size) #f)) ; the address space is 64kb
(define ppu-palettes (ppu-page))

(define (ppu-reset)
  ; allocate pages and put them into the memmap
  (define (install-ram from-address to-address)
    (for ([i (in-range (/ from-address ppu-page-size)
                       (/ to-address   ppu-page-size))])
      (vector-set! ppu-memmap i (ppu-page))))
  ; make memap entries point to already existing pages (thus introducing mirroring)
  (define (mirror-range from-address to-address  source)
    (define src (/ source ppu-page-size))
    (for ([i (in-range (/ from-address ppu-page-size)
                       (/ to-address   ppu-page-size))]
          [j (in-naturals)])
      (vector-set! ppu-memmap i (vector-ref ppu-memmap (+ src j)))))

  (install-ram  #x0000  #x2000)           ; Pattern Tables
  (install-ram  #x2000  #x3F00)           ; Name Tables
  ;             #x3F00  #x4000            ; Palettes (needs special handling)
  (mirror-range #x3000  #x3F00   #x2000)  ; Mirrors of name tables
  (mirror-range #x4000 #x10000   #x0000)  ; Mirrors bottom 16KB (four times)
  ; From https://wiki.nesdev.com/w/index.php/PPU_power_up_state
  ; Initial Register Values
  ; Register	At Power	After Reset
  ; PPUCTRL ($2000)	0000 0000	0000 0000
  ; XXX
  ; PPUMASK ($2001)	0000 0000	0000 0000
  ; PPUSTATUS ($2002)	+0+x xxxx	U??x xxxx
  ; OAMADDR ($2003)	$00	unchanged1
  ; $2005 / $2006 latch	cleared	cleared
  ; PPUSCROLL ($2005)	$0000	$0000
  ; PPUADDR ($2006)	$0000	unchanged
  ; PPUDATA ($2007) read buffer	$00	$00
  ; odd frame	no	no
  ; OAM	pattern	pattern
  ; NT RAM (external, in Control Deck)	mostly $FF	unchanged
  ; CHR RAM (external, in Game Pak)	unspecified pattern	unchanged
  )

  ; The palettes are only from $3F00 to $3F1F.
  ; The range $3F20-$3FFF mirrors $3F00-$3F1F, but since that's within a page,
  ; this needs to be handled in the load and store. We store #f in the
  ; memory map to indicate special handling.

(define (ppuload a) ; retrieve the byte value stored at address a
  (define bank (word>> a 8))                                 ; upper 8 bits = the bank number
  (define page (vector-ref ppu-memmap bank))                 ; the memmap has the page of the bank
  (if page
      (vector-ref page         (word-and a #b11111111))      ; lower 8 bits = position in page
      (vector-ref ppu-palettes (word-and a #b00011111))))    ; $0-$1f is 5 bits

(define (ppustore a b) ; store the byte b at address a
  ; (displayln (list 'ppustore a b) (current-error-port))
  (define bank (word>> (word-and #b1111111100000000 a) 8))   ; upper 8 bits = the bank number
  (define page (vector-ref ppu-memmap bank))                 ; the memmap has the page of the bank
  (if page
      (vector-set! page         (word-and a #b11111111) b)   ; lower 8 bits = position in page
      (vector-set! ppu-palettes (word-and a #b00011111) b))) ; $0-$1f is 5 bits

(ppu-reset)


;;;
;;; Addressing Modes
;;;

;                         EXAMPLES
(define immediate    0) ;   LDA  #$20
(define zero-page    1) ;   LDA   $20
(define zero-page-x  2) ;   LDA   $20,x
(define zero-page-y  3) ;   LDX   $20,y
(define absolute     4) ;   LDA $1234
(define absolute-x   5) ;   LDA $1234,x
(define absolute-y   6) ;   LDA $1234,y
(define indirect     7) ;   JMP ($1234)  (JMP only)
(define indirect-x   8) ;   LDA ($44,x)
(define indirect-y   9) ;   LDA ($44),y
(define relative    10) ;   BNE label
(define implied     11) ;   BRK
(define accumulator 12) ;   ROL A
(define todo        13)

;;;
;;; FETCH/DECODE/EXECUTE
;;;

(define opcode-modes    (make-bytes 256 todo))
(define opcode-sizes    (make-bytes 256 0))
(define opcode-cycles   (make-bytes 256 0))
(define opcode-handlers (for/vector ([i 256]) (λ _ (error 'opcode-handler (opcode-handler-error i)))))
(define (opcode-handler-error i) (~a "The opcode handler for opcode " i " has not been defined"))

(define trace-fuel 0)
(define (trace [n 10]) (set! trace-fuel n))

(define (step)
  ;; TODO handle interrupts here? Note - use exceptions and handle it in run.
  ; Note: The 6502 increments the PC first, then fetches the instruction  
  ;;; Uddate PC
  (PC!              (word+ PC 1))                        ; increment pc
  (unless (zero? trace-fuel)
    (displayln (disassemble-single PC))
    (set! trace-fuel (- trace-fuel 1)))
  (when (zero? trace-fuel) (raise 'done))
  (define pc        PC)                                  ; save old pc
  ;;; Fetch
  (define opcode    (load PC))                           ; fetch opcode
  ;;; Decode
  (define mode      (bytes-ref  opcode-modes    opcode)) ; find adressing mode
  (define size      (bytes-ref  opcode-sizes    opcode)) ; instruction size
  (define cycles    (bytes-ref  opcode-cycles   opcode)) ; clock cycles needed
  (define handle    (vector-ref opcode-handlers opcode)) ; does the work
  (set! cycle-count (+ cycle-count cycles))              ; increment clock
  ;;; Execute
  (define effective-operand
    ; todo: order these in most-used-first order
    (cond ;                                                        ; ***EXAMPLES***
      [(= mode immediate)                             (+ pc 1)]    ;  LDA  #$20
      [(= mode zero-page)                      (load  (+ pc 1))]   ;  LDA   $20
      [(= mode zero-page-x)           (byte+ X (load  (+ pc 1)))]  ;  LDA   $20,x
      [(= mode zero-page-y)           (byte+ Y (load  (+ pc 1)))]  ;  LDX   $20,y  (LDX, STX only)
      [(= mode absolute)                       (load2 (+ pc 1))]   ;  LDA $1234
      [(= mode absolute-x)            (word+ X (load2 (+ pc 1)))]  ;  LDA $1234,x  
      [(= mode absolute-y)            (word+ Y (load2 (+ pc 1)))]  ;  LDA $1234,y
      [(= mode indirect)    (load2bug          (load2 (+ pc 1)))]  ;  JMP ($1234)  (JMP only)
      [(= mode indirect-x)  (load2bug (word+ X (load  (+ pc 1))))] ;  LDA ($44,x)
      [(= mode indirect-y)  (word+ Y (load2bug (load  (+ pc 1))))] ;  LDA ($44),y
      [(= mode relative)         (let ([offset (load  (+ pc 1))])  ;  BNE label
                                   ; (displayln (list 'pc pc 'offset offset))
                                   (if (byte-neg? offset)
                                       (+ pc +1 offset (- #x100))
                                       (+ pc +1 offset)))]
      [(= mode implied)     #f]                                    ;  BRK
      [(= mode accumulator) #f]                                    ;  ROL A
      [else (error 'step (~a "Unhandled mode: " mode " Opcode: " opcode))]))
  ;;; Update PC before calling handler
  (when (> size 1) (PC! (word+ PC (- size 1))))
  (handle effective-operand)
  #;(displayln (~a "                                "
                   "P:" (number->string (flags->integer) 16) " " (~flags) " "
                   (~registers)))
  cycles)
  

;;;
;;; OPCODES / INSTRUCTIONS
;;;

; Main references used for the instruction table:
;   http://www.6502.org/tutorials/6502opcodes.html
; The remaining (undocumented) opcodes are still missing:
;   http://visual6502.org/wiki/index.php?title=6502_all_256_Opcodes


(define-syntax affects (syntax-rules ())) ; used as keyword

(define opcode-to-instruction-name-ht (make-hash)) ; for the disassembler
(define mnemonic-to-mode-to-opcode-ht (make-hash)) ; for the assembler
(define (register-mnemonic! mne mode opcode)
  (define (register mne)
    (define mode-to-opcode-ht (or (hash-ref mnemonic-to-mode-to-opcode-ht mne #f)
                                  (let ([ht (make-hash)])
                                    (hash-set! mnemonic-to-mode-to-opcode-ht mne ht)
                                    ht)))
    (hash-set! mode-to-opcode-ht mode opcode))
  (register (symbol-downcase mne))
  (register (symbol-upcase mne)))
(define (mnemonic+mode->opcode mne mode)  
  (define ht (hash-ref mnemonic-to-mode-to-opcode-ht mne))
  (hash-ref ht mode))
(define (has-mode? mne mode)
  (let ([mode-to-opcode-ht (hash-ref mnemonic-to-mode-to-opcode-ht mne #f)])
    (and mode-to-opcode-ht
         (hash-ref mode-to-opcode-ht mode #f)
         #t)))
(define (opcode->mnemonic opcode)
  (hash-ref opcode-to-instruction-name-ht opcode #f))

(define (reset)
  ; http://www.pagetable.com/?p=410
  ; Reset vector: $FFFC/$FFFD
  (PC! (load2 #xFFFC)))
         
(define (run start-address)
  (reset-status-register)
  (PC! (- start-address 1))
  (SP! #xff)   ; note: sp=$ff means address $01ff
  (continue))

(define nmi-due-to-vblank? #f)
(define (continue)
  (let loop ()
    ;(display "C")
    ; generate NMI due to vblank?
    (when nmi-due-to-vblank?
      ; (displayln 'NMI (current-error-port))
      (set! nmi-due-to-vblank? #f)
      (handle-nmi))
    ; business as usual
    (let cpu-loop ([fuel 113])
      (unless (zero? fuel)
        (step)
        (cpu-loop (- fuel 1))))
    ;(display "P")
    (ppu-step 1364)
    (loop)))

(define-syntax (define-opcodes stx)
  (define-syntax-class mnemonic
    (pattern mnemonic:id #:with name (syntax-upcase stx #'mnemonic)))
  (define-syntax-class opcode-specification
    (pattern (mode opcode size cycles)       #:with extra-cycles #'0)
    (pattern (mode opcode size cycles extra) #:with extra-cycles #'extra))  
  (define-syntax-class flag
    #:literals   (C Z I D B V S)
    (pattern (~or C Z I D B V S)))
  (syntax-parse stx
    #:literals (affects)
    [(_define-opcodes register-opcode-handlers
                      (NAME:mnemonic (affects f:flag ...) (spec:opcode-specification ...)) ...)
     #'(begin
         (let ([name 'NAME.name])
           (hash-set!  opcode-to-instruction-name-ht spec.opcode name)        ...
           (bytes-set! opcode-sizes                  spec.opcode spec.size)   ...
           (bytes-set! opcode-cycles                 spec.opcode spec.cycles) ...
           (bytes-set! opcode-modes                  spec.opcode spec.mode)   ...           
           (register-mnemonic! name spec.mode spec.opcode) ...)         
         ...
         (define (register-opcode-handlers)
           (let ([Name NAME.name]) (vector-set! opcode-handlers spec.opcode Name) ...)
           ...))]))

(define-opcodes
  register-opcode-handlers ; use this after all instructions are defined
  (STOP (affects) ((implied #xff 1 1)))   ; fake instruction - emulator only
  (ADC ; Add with carry
      (affects S V Z C)
      ; (mode hex size cycles extra-cycle-on-page-crossed
      ((immediate   #x69 2 2)
       (zero-page   #x65 2 3)
       (zero-page-x #x75 2 4)
       (absolute    #x6d 3 4)
       (absolute-x  #x7d 3 4 1)  ; 1 means extra cycle 
       (absolute-y  #x79 3 4 1)  ; on crossed page boundary
       (indirect-x  #x61 2 6)
       (indirect-y  #x71 2 5 1)))
  (AND ; bitwise and with accumulator
      (affects S Z)
      ((immediate   #x29 2 2)
       (zero-page   #x25 2 3)
       (zero-page-x #x35 2 4)
       (absolute    #x2d 3 4)
       (absolute-x  #x3d 3 4 1)
       (absolute-y  #x39 3 4 1)
       (indirect-x  #x21 2 6)
       (indirect-y  #x31 2 5 1)))
  (ASL ; arithmetic shift left
      (affects S Z C)
      ((accumulator #x0a 1 2)
       (zero-page   #x06 2 5)
       (zero-page-x #x16 2 6)
       (absolute    #x0e 3 6)
       (absolute-x  #x1e 3 7)))
  (BIT ; test bits
      (affects S V Z)
    ((zero-page   #x24 2 3)
     (absolute    #x2c 3 4)))
  ;;; BRANCH INSTRUCTIONS
  ;;;   branch not taken:  2 cycles
  ;;;   branch     taken:  3 cycles
  ;;;                     +1 if page boundary crossed
  (BPL (affects) ((relative #x10 2 2 1))) ; plus
  (BMI (affects) ((relative #x30 2 2 1))) ; minus
  (BVC (affects) ((relative #x50 2 2 1))) ; overflow clear
  (BVS (affects) ((relative #x70 2 2 1))) ; overflow set
  (BCC (affects) ((relative #x90 2 2 1))) ; carry clear
  (BCS (affects) ((relative #xb0 2 2 1))) ; carry set
  (BNE (affects) ((relative #xd0 2 2 1))) ; not equal
  (BEQ (affects) ((relative #xf0 2 2 1))) ; equal

  
  (BRK ; Break - causes non-maskable interupt
      (affects B)
    ((implied #x00 1 7)))
    
  (CMP ; compare accumulator
      (affects S Z C)
      ((immediate   #xc9 2 2)
       (zero-page   #xc5 2 3)
       (zero-page-x #xd5 2 4)
       (absolute    #xcd 3 4)
       (absolute-x  #xdd 3 4 1)
       (absolute-y  #xd9 3 4 1)
       (indirect-x  #xc1 2 6)
       (indirect-y  #xd1 2 5 1)))
  (CPX ; compare X register
      (affects S Z C)
      ((immediate   #xe0 2 2)
       (zero-page   #xe4 2 3)
       (absolute    #xec 3 4)))
  (CPY ; compare Y register
      (affects S Z C)
      ((immediate   #xc0 2 2)
       (zero-page   #xc4 2 3)
       (absolute    #xcc 3 4)))
  (DEC ; decrement memory
      (affects S Z)
      ((zero-page   #xc6 2 5)
       (zero-page-x #xd6 2 6)
       (absolute    #xce 3 6)
       (absolute-x  #xde 3 7)))
  (INC ; increment memory
      (affects S Z)
      ((zero-page   #xe6 2 5)
       (zero-page-x #xf6 2 6)
       (absolute    #xee 3 6)
       (absolute-x  #xfe 3 7)))
  (EOR ; bitwise exclusive or
      (affects S Z)
      ((immediate   #x49 2 2)
       (zero-page   #x45 2 3)
       (zero-page-x #x55 2 4)
       (absolute    #x4d 3 4)
       (absolute-x  #x5d 3 4 1)
       (absolute-y  #x59 3 4 1)
       (indirect-x  #x41 2 6)
       (indirect-y  #x51 2 5 1)))
  ;;; STATUS / FLAG INSTRUCTIONS
  (CLC (affects C) ((implied #x18 1 2))) ; clear carry
  (SEC (affects C) ((implied #x38 1 2))) ; set   carry
  (CLI (affects I) ((implied #x58 1 2))) ; clear interrupt
  (SEI (affects I) ((implied #x78 1 2))) ; set   interrupt
  (CLV (affects V) ((implied #xb8 1 2))) ; clear overflow
  (CLD (affects D) ((implied #xd8 1 2))) ; clear decimal
  (SED (affects D) ((implied #xf8 1 2))) ; set   decimal

  (JMP ; jump
      (affects) 
      ((absolute    #x4c 3 6)
       (indirect    #x6c 3 5)))
  (JSR ; jump to subroutine
      (affects)
      ((absolute    #x20 3 6)))

  (LDA ; load accumulator
      (affects S Z)
      ((immediate   #xa9 2 2)
       (zero-page   #xa5 2 3)
       (zero-page-x #xb5 2 4)
       (absolute    #xad 3 4)
       (absolute-x  #xbd 3 4 1)
       (absolute-y  #xb9 3 4 1)
       (indirect-x  #xa1 2 6)
       (indirect-y  #xb1 2 5 1)))
  (LDX ; load X register
      (affects S Z)
      ((immediate   #xa2 2 2)
       (zero-page   #xa6 2 3)
       (zero-page-y #xb6 2 4)
       (absolute    #xae 3 4)
       (absolute-y  #xbe 3 4 1)))
  (LDY ; load Y register
      (affects S Z)
      ((immediate   #xa0 2 2)
       (zero-page   #xa4 2 3)
       (zero-page-x #xb4 2 4)
       (absolute    #xac 3 4)
       (absolute-x  #xbc 3 4 1)))
  (LSR ; logical shift right
      (affects S Z C)
      ((accumulator #x4a 1 2)
       (zero-page   #x46 2 5)
       (zero-page-x #x56 2 6)
       (absolute    #x4e 3 6)
       (absolute-x  #x5e 3 7)))
  (NOP ; no operation
      (affects)
    ((implied       #xea 1 2)))
  (ORA ; bitwise or with accumulator
      (affects S Z)
      ((immediate   #x09 2 2)
       (zero-page   #x05 2 3)
       (zero-page-x #x15 2 4)
       (absolute    #x0d 3 4)
       (absolute-x  #x1d 3 4 1)
       (absolute-y  #x19 3 4 1)
       (indirect-x  #x01 2 6)
       (indirect-y  #x11 2 5 1)))
  ;;; REGISTER INSTRUCTIONS
  (TAX (affects S Z) ((implied #xaa 1 2))) ; transfer a to x
  (TXA (affects S Z) ((implied #x8a 1 2))) ; transfer x to a
  (DEX (affects S Z) ((implied #xca 1 2))) ; decrement x
  (INX (affects S Z) ((implied #xe8 1 2))) ; increment x
  (TAY (affects S Z) ((implied #xa8 1 2))) ; transfer a to y
  (TYA (affects S Z) ((implied #x98 1 2))) ; transfer y to a
  (DEY (affects S Z) ((implied #x88 1 2))) ; decrement y
  (INY (affects S Z) ((implied #xc8 1 2))) ; increment y

  (ROL ; rotate left
      (affects S Z C)
      ((accumulator #x2a 1 2)
       (zero-page   #x26 2 5)
       (zero-page-x #x36 2 6)
       (absolute    #x2e 3 6)
       (absolute-x  #x3e 3 7)))
  (ROR ; rotate right
      (affects S Z C)
      ((accumulator #x6a 1 2)
       (zero-page   #x66 2 5)
       (zero-page-x #x76 2 6)
       (absolute    #x6e 3 6)
       (absolute-x  #x7e 3 7)))

  (RTI ; return from interrupt
      (affects C Z I D B V S)
    ((implied #x40 1 6)))
  (RTS ; return from subroutine
      (affects)
    ((implied #x60 1 6)))

  (SBC ; subtract with carry
      (affects S V Z C)
    ((immediate   #xe9 2 2)
     (zero-page   #xe5 2 3)
     (zero-page-x #xf5 2 4)
     (absolute    #xed 3 4)
     (absolute-x  #xfd 3 4 1)
     (absolute-y  #xf9 3 4 1)
     (indirect-x  #xe1 2 6)
     (indirect-y  #xf1 2 5 1)))
  (STA ; store accumulator
      (affects)
    ((zero-page   #x85 2 3)
     (zero-page-x #x95 2 4)
     (absolute    #x8d 3 4)
     (absolute-x  #x9d 3 5)
     (absolute-y  #x99 3 5)
     (indirect-x  #x81 2 6)
     (indirect-y  #x91 2 6)))

  ;;; STACK INSTRUCTIONS
  ; TODO: look up flags affected
  (TXS (affects) ((implied #x9a 1 2))) ; transfer X to SP
  (TSX (affects) ((implied #xba 1 2))) ; transfer SP to X
  (PHA (affects) ((implied #x48 1 3))) ; push A
  (PLA (affects) ((implied #x68 1 4))) ; pull A
  (PHP (affects) ((implied #x08 1 3))) ; push status
  (PLP (affects) ((implied #x28 1 4))) ; pull status

  (STX ; store X register
      (affects)
    ((zero-page   #x86 2 3)
     (zero-page-y #x96 2 4)
     (absolute    #x8e 3 4)))
  (STY ; store Y register
      (affects)
    ((zero-page   #x84 2 3)
     (zero-page-x #x94 2 4)
     (absolute    #x8c 3 4))))

;;;
;;; INSTRUCTIONS
;;;

;;; Reference: http://www.6502.org/tutorials/6502opcodes.html

(define-syntax (define-instruction stx)
  (define-syntax-class mnemonic
    (pattern mnemonic:id #:with name (syntax-upcase stx #'mnemonic)))
  (syntax-parse stx
    ; Most adressing modes result in a an adress adr
    [(_define-instruction (mne:mnemonic adr) . body)
     #'(define (mne.name adr) #;(displayln (list 'mne adr)) . body)]
    ; The addression mode "implied" has no adress.
    [(_define-instruction (mne:mnemonic) . body)
     #'(define (mne.name) #;(displayln (list 'mne)) . body)]))

; TODO: Handle cycles on branch operations
(define-syntax (extra-cycle stx) (syntax-parse stx [(_extra-cycle) #'(void)]))

;;; EMULATOR ONLY
(define-instruction (stop a) (raise 'stop)) ; stop emulation

;;; MOVE INSTRUCTIONS
(define-instruction (sta a)                                                (store a A))
(define-instruction (stx a)                                                (store a X))
(define-instruction (sty a)                                                (store a Y))
(define-instruction (lda a) (let ([v (load a)])                   (A! v) (S! v) (Z! v)))
(define-instruction (ldx a) (let ([v (load a)])                   (X! v) (S! v) (Z! v)))
(define-instruction (ldy a) (let ([v (load a)])                   (Y! v) (S! v) (Z! v)))
(define-instruction (tax _)                                       (X! A) (S! X) (Z! X))
(define-instruction (tay _)                                       (Y! A) (S! Y) (Z! Y))
(define-instruction (txa _)                                       (A! X) (S! A) (Z! A))
(define-instruction (tya _)                                       (A! Y) (S! A) (Z! A))
(define-instruction (pla _)   (let ([v (pull!)])                  (A! v) (S! v) (Z! v)))
(define-instruction (tsx _)   (let ([v (pull!)])                  (X! v) (S! v) (Z! v)))
(define-instruction (pha _)                                                  (push! A))
(define-instruction (txs _)                                                  (push! X))
(define-instruction (bit a) (let ([v (load a)])
                              (S! v)
                              (if (= (byte-and v #b01000000) #b01000000) (V! 1) (V! 0))
                              (Z! (byte-and v A))))

;;; LOGICAL AND ARITHMETICAL
(define-instruction (ora a) (let ([v (byte-or  A (load a))])    (A! v) (S! v) (Z! v)))
(define-instruction (and a) (let ([v (byte-and A (load a))])    (A! v) (S! v) (Z! v)))
(define-instruction (eor a) (let ([v (byte-xor A (load a))])    (A! v) (S! v) (Z! v)))
(define-instruction (cmp a) (let ([v (byte-    A (load a))])    (C! v) (S! v) (Z! v)))
(define-instruction (cpx a) (let ([v (byte-    X (load a))])    (C! v) (S! v) (Z! v)))
(define-instruction (cpy a) (let ([v (byte-    Y (load a))])    (C! v) (S! v) (Z! v)))
(define-instruction (dex _) (let ([v (byte-dec X)])             (X! v) (S! v) (Z! v)))
(define-instruction (inx _) (let ([v (byte-inc X)])             (X! v) (S! v) (Z! v)))
(define-instruction (dey _) (let ([v (byte-dec Y)])             (Y! v) (S! v) (Z! v)))
(define-instruction (iny _) (let ([v (byte-inc Y)])             (Y! v) (S! v) (Z! v)))
(define-instruction (dec a) (let ([v (byte-dec (load a))]) (store a v) (S! v) (Z! v)))
(define-instruction (inc a) (let ([v (byte-inc (load a))]) (store a v) (S! v) (Z! v)))
(define-instruction (adc a) (adc-body           (load a)))
(define-instruction (sbc a) (adc-body (byte-neg (load a))))
(define (adc-body v)
  ; Note: The NES doesn't support decimal mode, so the D flag is ignored.
  ; Formulas for overflow flag:
  ;     http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
  (let* ([c (if (C?) 1 0)]
         [t (+ A v c)]
         [s (byte t)])
    (if (> t #xff) (set-C) (clear-C))
    ; TODO : Use one of the efficient formulas for V instead
    (V! (if (or (and (byte-neg? A) (byte-neg? v) (byte-pos? s))
                (and (byte-pos? A) (byte-pos? v) (byte-neg? s)))
            1 0))
    (A! s)
    (Z! s)
    (S! t)))
(define-instruction (ror a)
  (let* ([v (if a (load a) A)]
         [w (byte-ror v (C?))])
    (if (odd? v) (set-C) (clear-C))
    (S! w)
    (Z! w)
    (if a (store a w) (A! w))))
(define-instruction (rol a)
  (let* ([v (if a (load a) A)]
         [w (byte-rol v (C?))]) 
    (if (byte-msb? v) (set-C) (clear-C))
    (S! w)
    (Z! w)
    (if a (store a w) (A! w))))
(define-instruction (lsr a)
  (let* ([v (if a (load a) A)]
         [w (byte-lsr v)])
    (if (odd? v) (set-C) (clear-C))
    (S! w)
    (Z! w)
    (if a (store a w) (A! w))))
(define-instruction (asl a)
  (let* ([v (if a (load a) A)]
        [w (byte-asl v)])
    (if (byte-msb? v) (set-C) (clear-C))
    (S! w)
    (Z! w)
    (if a (store a w) (A! w))))

;;; CONTROL
; Note: When the addressing mode is relative, a is the pc+displacement
(define-instruction (bpl a) (unless (S?)     (PC! a)))
(define-instruction (bmi a) (when   (S?)     (PC! a)))
(define-instruction (bvc a) (when   (= V 0)  (PC! a)))
(define-instruction (bvs a) (when   (= V 1)  (PC! a)))
(define-instruction (bcc a) (unless (C?)     (PC! a)))
(define-instruction (bcs a) (when   (C?)     (PC! a)))
(define-instruction (bne a) (unless (Z?)     (PC! a)))
(define-instruction (beq a) (when   (Z?)     #;(displayln (list 'HERE 'PC PC 'a a)) (PC! a)))
(define-instruction (brk _)
  (let ([pc+2 (+ PC 2)] ; todo: only +1 here?
        [sr ; status register as integer
         (+ (if (C?)   1 0)
            (if (Z?)   2 0)
            (if (I?)   4 0)
            (if (D?)   8 0)   ; D = 1 on the NES
            16                ; B = 1 when PHP or BRK is used
            32                ; U, unused, that is, always set
            (if (V?)  64 0)
            (if (S?) 128 0))])    
    (push! (high pc+2))
    (push! (low  pc+2))
    (push! sr)
    (set-B) ; set break flag
    (PC! (word- (word (load #xFFFF) (load #xFFFE)) 1))))
(define (handle-nmi)
  (let ([pc (+ PC 1)]   ; RTI will subtract 1
        [sr ; status register as integer
         (+ (if (C?)   1 0)
            (if (Z?)   2 0)
            (if (I?)   4 0)
            (if (D?)   8 0)   ; D = 1 on the NES
            0                 ; B = 1 when PHP or BRK is used
            32                ; U, unused, that is, always set
            (if (V?)  64 0)
            (if (S?) 128 0))])    
    (push! (high pc))
    (push! (low  pc))
    (push! sr)
    ; (set-B) ; set break flag
    (PC! (word- (word (load #xFFFB) (load #xFFFA)) 1))))
(define-instruction (rti _); (affects C Z I D B V S)
  (let ([sr (pull!)] [l  (pull!)] [h  (pull!)])
    (if (bit-clear? sr 0) (clear-C) (set-C))
    (if (bit-clear? sr 1) (clear-Z) (set-Z))
    (if (bit-clear? sr 2) (clear-I) (set-I))
    ; (if (bit-clear? sr 3) (clear-D) (set-D)) ; not on the NES
    (if (bit-clear? sr 4) (clear-B) (set-B))
    ; (if (bit-clear? sr 5) (clear-U) (set-U)) ; unused flag always 1
    (if (bit-clear? sr 6) (clear-V) (set-V))
    (if (bit-clear? sr 7) (clear-S) (set-S))
    (PC! (- (word h l) 1))))
; TODO: check that we are in fact pushing the correct PC
(define-instruction (jmp a) (PC! (- a 1))) ; this must match handling of pc in step
(define-instruction (jsr a) (push! (high PC)) (push! (low PC)) (PC! (- a 1)))
(define-instruction (rts _) (let ([l (pull!)] [h (pull!)]) (PC! (word h l))))
(define-instruction (nop _) (void))
;;; STATUS REGISTER  
(define-instruction (clc _) (clear-C))
(define-instruction (sec _) (set-C))
(define-instruction (cld _) (clear-D))
(define-instruction (sed _) (set-D))
(define-instruction (cli _) (clear-I))
(define-instruction (sei _) (set-I))
(define-instruction (clv _) (clear-V))
(define-instruction (php a)
  (push! (+ (if (C?)   1 0)
            (if (Z?)   2 0)
            (if I      4 0)
            (if (D?)   8 0)
            ; 8                 ; D = 1 on the NES
            16                ; B = 1 when PHP or BRK is used
            32                ; U, unused, that is, always set
            (if (V?)  64 0)
            (if (S?) 128 0))))
(define-instruction (plp a)
  (let ([b (pull!)])
    (if (zero? (bitand b   1)) (clear-C) (set-C))
    (if (zero? (bitand b   2)) (clear-Z) (set-Z))    
    (if (zero? (bitand b   4)) (clear-I) (set-I))
    (if (zero? (bitand b   8)) (clear-D) (set-D))
    (if (zero? (bitand b  16)) (clear-B) (set-B))
    ; ignore U
    (if (zero? (bitand b  64)) (clear-V) (set-V))
    (if (zero? (bitand b 128)) (clear-S) (set-S))))
    

; Now that the instructions are defined, we can associate each opcode
; with its handler.

(register-opcode-handlers)

;;;
;;; DISASSEMBLE
;;;

(define (disassemble-single a)
  ; Disassemble a single instruction
  (define opcode    (load a))                            ; fetch opcode
  (define mode      (bytes-ref  opcode-modes    opcode)) ; find adressing mode
  (define size      (bytes-ref  opcode-sizes    opcode)) ; instruction size
  (define b1 (and (> size 1) (load (+ a 1))))
  (define b2 (and (> size 2) (load (+ a 2))))
  (define b1$ (and b1 (~a "$" (hex2 b1))))
  (define b2$ (and b2 (~a "$" (hex2 b2))))
  (define b$  (and b1 b2 (~a "$" (hex4 (word b2 b1)))))
  (define (br+ a x) (if (byte-neg? x) (+ a x (- #x100) 2) (+ a x 2)))
  ; (displayln (list 'opcode opcode 'mode mode 'size size b1 b2))
  (define effective-operand
    ; todo: order these in most-used-first order
    (cond ;                                                          ; ***EXAMPLES***
      [(= mode immediate)           (list   (list 'quote b1$))]      ;  LDA  #$20
      [(= mode zero-page)           (list                  b1$)]     ;  LDA   $20
      [(= mode zero-page-x)         (list                  b1$ 'x)]  ;  LDA   $20,x
      [(= mode zero-page-y)         (list                  b1$ 'y)]  ;  LDX   $20,y  (LDX, STX only)
      [(= mode absolute)            (list                   b$   )]  ;  LDA $1234
      [(= mode absolute-x)          (list                   b$ 'x)]  ;  LDA $1234,x  
      [(= mode absolute-y)          (list                   b$ 'y)]  ;  LDA $1234,y
      [(= mode indirect)            (list             (list b$)  )]  ;  JMP ($1234)  (JMP only)
      [(= mode indirect-x)          (list            (list b1$ 'x))] ;  LDA ($44,x)
      [(= mode indirect-y)          (list            (list b1$ 'y))] ;  LDA ($44),y
      [(= mode relative)            (list        (hex4 (br+ a b1)))] ;  RELATIVE BRANCHING
      [(= mode implied)             (list)]                          ;  BRK
      [(= mode accumulator)         (list 'A)]                       ;  ROL A
      [else (error 'step (~a "Unhandled mode: " mode " Opcode: " opcode))]))
  (define mnemonic (opcode->mnemonic opcode))
  (define (hex2* n) (if n (~a (hex2 n) " ") "   "))
  (list (string-append (hex4 a) "  " (hex2* opcode) (hex2* b1) (hex2* b2))
        (cons mnemonic effective-operand)))
  

(define (mem-dump a [lines 8])
  (define (byte a)   (hex (load (word-and a #xFFFF))))
  (define (bytes4 a) (~a (byte a) " " (byte (+ a 1)) " " (byte (+ a 2)) " " (byte (+ a 3)) " "))
  (define (printable? c) (regexp-match #px"[ -~]" (string c)))
  (define (ch x) (let ([c (integer->char x)]) (if (printable? c) c #\.)))
  (define (str a) (apply string (for/list ([x 16]) (ch (load (word-and (+ a x) #xFFFF))))))
  (string-append*
   (for/list ([l lines])
     (let ([a (+ a (* l 16))])
       (define bytes
         (~a (bytes4 a) " " (bytes4 (+ a 4)) " " (bytes4 (+ a 8)) " " (bytes4 (+ a 12)) " "))
       (~a (hex4 a) "  " bytes "  " (str a) "\n")))))

(define (ppu-mem-dump a [lines 8])
  (define (byte a)   (hex (ppuload (word-and a #xFFFF))))
  (define (bytes4 a) (~a (byte a) " " (byte (+ a 1)) " " (byte (+ a 2)) " " (byte (+ a 3)) " "))
  (define (printable? c) (regexp-match #px"[ -~]" (string c)))
  (define (ch x) (let ([c (integer->char x)]) (if (printable? c) c #\.)))
  (define (str a) (apply string (for/list ([x 16]) (ch (ppuload (word-and (+ a x) #xFFFF))))))
  (string-append*
   (for/list ([l lines])
     (let ([a (+ a (* l 16))])
       (define bytes
         (~a (bytes4 a) " " (bytes4 (+ a 4)) " " (bytes4 (+ a 8)) " " (bytes4 (+ a 12)) " "))
       (~a (hex4 a) "  " bytes "  " (str a) "\n")))))



;;;
;;; ASSEMBLER
;;;

; (define immediate    0)
; (define zero-page    1)
; (define zero-page-x  2) ; aka pre-indexed indirect
; (define zero-page-y  3) ; aka pre-indexed indirect
; (define absolute     4)
; (define absolute-x   5)
; (define absolute-y   6) 
; (define indirect     7)
; (define indirect-x   8) ; modeIndexedIndirect
; (define indirect-y   9) ; modeIndirectIndexed
; (define relative    10)
; (define implied     11)
; (define accumulator 12)
; (define todo        13)


; | Addressing Mode | SEXP-based format | String format  |
; |-----------------|-------------------|----------------|
; |   Implied       |  (brk)            | "brk"          |

; |   Immediate     |  (lda $00)        | "lda #$00"     |
; |   Accumulator   |  (rol A)          | "rol a"        |
; |   Zero-page     |  (lda $03)        | "lda $03"      |
; |   Zero-page, X  |  (lda $03     x)  | "lda $03, x"   |
; |   Zero-page, Y  |  (ldx $03     y)  | "ldx $03, y"   |
; |   Absolute      |  (sbc $0001)      | "sbc $0001"    |
; |   Absolute, X   |  (lda $1234   x)  | "lda $1234, x" |
; |   Absolute, Y   |  (lda $1234   y)  | "lda $1234, y" |
; |   Indirect      |  (jmp ($1234) )   | "jmp ($1234)   |
; |   Indirect, X   |  (lda ($12)   x)  | "lda ($12), x" |
; |   Indirect, Y   |  (lda ($34)   y)  | "lda ($34), y" |
; |   Relative      |  (bne fd)         | "bne &fd"      |

(define (literal lit [signal-error? #t])
  (cond
    [(number? lit) lit]
    [(symbol? lit) (literal (symbol->string lit))]
    [(string? lit) (match lit
                     [(regexp #rx"\\$([0-9a-fA-F]*)" (list all hex)) (string->number hex 16)]
                     [(regexp #rx"([0-9]*)"          (list all dec)) (string->number dec 10)]
                     [else (if signal-error? (error 'literal lit) #f)])]
    [else          (error 'literal "expected number, got ~a" lit)]))

(define (assembler lines [pass 1] [symbol-table (make-hash)])
  (when (= pass 2) (displayln symbol-table))
  ;; Pass 1 and 2 are almost identical.
  ;; When pass 1 begins the symbol table is empty.
  ;; When pass 2 begins the symbol table contains all labels seen in pass 1,
  ;; which means jumps and branches can be resolved.
  (define cur 0)  
  (define (label? sym)         (and (symbol? sym) (regexp-match #px"^.*[:]$" (symbol->string sym))))
  (define (label-name sym)     (string->symbol (second (regexp-match #px"^(.*)[:]$" (~a sym)))))
  (define (resolve sym)        (hash-ref symbol-table sym (if (= pass 1) 0
                                                              (begin
                                                                (displayln sym)
                                                                #f))))
  (define (assemble-all lines) (for/list ([line lines]) (assemble-line line)))
  (define (pick-mode mne adr zp-mode abs-mode)
    (if (and (has-mode? mne zp-mode) (<= 0 adr 255))  zp-mode  abs-mode))
  (define (assemble-line line)
    ; (displayln (list 'assemble-line line))
    (match line
      [(list '* '= adr)                (set! cur (literal adr)) `(* = ,(literal adr))]
      [lab #:when (label? lab) (when (= pass 1) (hash-set! symbol-table (label-name lab) cur))  lab]
      [(list mne)                      (assemble-instruction line implied     mne)]
      [(list mne 'A)                   (assemble-instruction line accumulator mne)]
      [(list mne 'a)                   (assemble-instruction line accumulator mne)]
      [(list mne (list 'quote const))  (assemble-instruction line immediate   mne (literal const))]
      [(list mne (list adr))           (assemble-instruction line indirect    mne (literal adr))]
      [(list mne (list adr (or 'x 'X)))(assemble-instruction line indirect-x  mne (literal adr))]
      [(list mne (list adr)(or 'y 'Y)) (assemble-instruction line indirect-y  mne (literal adr))]
      [(list mne offset)
       #:when (has-mode? mne relative)
       (let ([offset (if (symbol? offset) (resolve offset) offset)])
         (assemble-instruction line relative  mne (literal offset)))]
      [(list mne adr)
       (let* ([a (or (literal adr #f) (resolve adr))] [mode (pick-mode mne a zero-page absolute)])
         (assemble-instruction line mode mne a))]
      [(list mne adr (or 'x 'X))
       (let* ([a (or (literal adr #f) (resolve adr))] [mode (pick-mode mne a zero-page-x absolute-x)])
         (assemble-instruction line mode mne a))]
      [(list mne adr (or 'y 'Y))
       (let* ([a (or (literal adr #f) (resolve adr))] [mode (pick-mode mne a zero-page-y absolute-y)])
         (assemble-instruction line mode mne a))]
      [_ (error 'assembler "got: ~a " line)]))
  (define (assert-mode line mne mode)
    (unless (has-mode? mne mode)
      (displayln (list 'assert-mode 'line line))
      (error 'assembler (~a "The mode " mode " is not a legal addressing mode for " mne))))
  (define (assemble-instruction line mode mne [operand 0])
    ; (displayln (list 'assemble-instruction 'operand operand))
    ; (displayln (list 'ai 'line line))
    (assert-mode line mne mode)
    (define opcode (mnemonic+mode->opcode mne mode))
    (define operand-bytes
      (cond        
        [(member mode (list accumulator implied))                     '()]
        [(member mode (list immediate indirect-x indirect-y ))        (list operand)]
        [(member mode (list indirect absolute absolute-x absolute-y)) (if operand
                                                                          (list (low operand)
                                                                                (high operand))
                                                                          (list 0 0))]
        [(member mode (list zero-page zero-page-x zero-page-y))       (list operand)]
        [(member mode (list relative))                                (list (byte (- operand cur 2)))]
        [else (displayln (list 'assembler 'line line 'mne mne 'mode mode 'opcode opcode))
              (error 'assembler "unexpected mode?")]))
    (let ([c cur])
      (unless (= (+ (length operand-bytes) 1) (bytes-ref opcode-sizes opcode))
        (displayln line) (error 'assembler))
      (set! cur (+ cur 1 (length operand-bytes)))
      (cons opcode operand-bytes)
      ; Use (cons c version to get addresses for each line
      #;(list (hex4 c) line (list (map hex2 (cons opcode operand-bytes))))))
  (cond
    [(= pass 1) (assemble-all lines)
                (assembler lines 2 symbol-table)]
    [(= pass 2) (assemble-all lines)]))

(define (install-opcodes-from-assembler instructions [cur-pc 0])
  (define cur cur-pc)
  (for ([instruction instructions])
    (match instruction
      [(list '* '= adr) (set! cur adr)]
      [(list b1)        (store cur b1)
                        (set! cur (+ cur 1))]
      [(list b1 b2)     (store cur b1) (store (+ cur 1) b2)
                        (set! cur (+ cur 2))]
      [(list b1 b2 b3)  (store cur b1) (store (+ cur 1) b2) (store (+ cur 2) b3)
                        (set! cur (+ cur 3))]
      [label #:when (symbol? label) (void)]
      [_ (displayln instruction) (error 'install-opcodes-from-assembler)])))

(define (assembler->traditional sexp-lines)
  (define (to-hex n) (if (symbol? n) n (~a "$" (number->string n 16))))
  (define (to-traditional s)
    (match s 
      [(list '* '= a)                 (~a "* = " a)]  
      [(list mne 'A)                  (~a mne " A")] ; accumulator
      [(list mne 'a)                  (~a mne " a")]
      [(list mne (list 'quote const)) (~a mne " #" (to-hex const)    )]
      [(list mne (list adr))          (~a mne " (" (to-hex adr)   ")")]
      [(list mne (list adr  'x))      (~a mne " (" (to-hex adr) ",x)")]
      [(list mne (list adr) 'y)       (~a mne " (" (to-hex adr) "),y")]
      [(list mne adr)                 (~a mne " "  (to-hex adr)      )]
      [(list mne adr 'x)              (~a mne " "  (to-hex adr) ",x" )]
      [(list mne adr 'y)              (~a mne " "  (to-hex adr) ",y" )]
      [_else (displayln s)
             (error 'sexp-source->traditional "missed an addressing mode?")]))
  (apply string-append
         (for/list ([line sexp-lines])
           (string-append (to-traditional line) "\n"))))

; ADDRESSING MODE   TRADITIONAL    SEXP
; immediate    0    LDA #$20       (LDA  '$20)
; zero-page    1    LDA   $20      (LDA   $20)
; zero-page-x  2    LDA   $20,x    (LDA   $20 x)    
; zero-page-y  3    LDX   $20,y    (LDA   $20 y)
; absolute     4    LDA $1234      (LDA $1234)
; absolute-x   5    LDA $1234,x    (LDA $1234 x)
; absolute-y   6    LDA $1234,y    (LDA $1234 y)
; indirect     7    JMP ($1234)    (JMP ($1234))
; indirect-x   8    LDA ($44,x)    (LDA ($44 x)
; indirect-y   9    LDA ($44),y    (LDA ($44) y)
; relative    10    BNE label      (BNE label)
; implied     11    BRK            (BRK)
; accumulator 12    ROL A          (ROL A)

(define (traditional->assembler lines)
  ;;; The following syntax is a very small subset of the syntax expected by cc65.
  ; [] means optional
  ; <line>      ::= <directive> | <label> | [<label>] <mnemonic>
  ; <label>     ::= <name>:                                   ; a label is a name followed by a colon 
  ; <directive> ::=       * = <address>                       ; pc at start of line
  ;              |     name = <number>                        ; symbolic constant
  ; <number>     The $ and h prefix means hexadecimal number  ; hex numbers
  ;              The % prefix means binary                    ; binary numbers
  ;              A bare number is a decimal number            ; decimal numbers
  ;
  (define (convert-line line)
    (let ([line (skip-whitespace line)])
      (or (lex-star-line line)
          (match (lex-label line)
            [(list label rest)
             (define after-label
               (match (lex-mnemonic (skip-whitespace rest))
                 [(list #f  rest) '()]
                 [(list mne rest) (match (lex-operand (skip-whitespace rest))
                                    [(list #f) (list mne)]         ; implied
                                    [operand   (cons mne operand)])]))
             (if label
                 (cons label after-label)
                 after-label)]))))
  (define (lex-star-line line)
    (match (regexp-match #px"^\\*[ \t]*=[ \t]*(.*)$" line)
      [(list _ rest) (list* '* '= (lex-operand (skip-whitespace rest)))]
      [_             #f]))
  (define (lex-label line)
    (match (regexp-match #px"^(\\D\\S*):(.*)$" line)
      [(list _ label rest) (list label rest)]
      [_                   (list #f    line)]))
  (define (skip-whitespace line)
    (second (regexp-match #px"^\\s*(.*)$" line)))
  (define (lex-mnemonic line)
    (match (regexp-match #px"^(\\D\\D\\D)(.*)$" line)
      [(list _ mne rest) (list (string->symbol mne) rest)]
      [_                 (list #f line)]))
  (define (lex-number line)
    (let ([str (skip-whitespace line)])
      (match (regexp-match #px"^([$h][0-9a-fA-F]+)(.*)$" line)     ; hex
        [(list _ operand rest) (string->symbol operand)]
        [_ (match (regexp-match #px"^[%]([01]+)(.*)$" line)        ; binary
             [(list _ operand rest) (string->number operand 2)]
             [_ (match (regexp-match #px"^([0-9]+)(.*)$" line)     ; decimal
                  [(list _ operand rest) (string->number operand)]
                  [_ (match (regexp-match #px"^([a-zA-Z][a-zA-Z0-9_]*)(.*)$" line)
                       [(list _ reference more) (string->symbol reference)]
                       [_ #f])])])])))
  (define (lex-operand line)
    (displayln line)
    (match (regexp-match #px"^#(.*)$" line)                                       ; immediate
      [(list _ rest) (match (lex-number rest)
                       [#f "ERROR: number after # missing"]
                       [n   (list (list 'quote n))])]
      [_ (match (regexp-match #px"^[(](.*)[)][ \t]*,[ \t]*([yY])(.*)$" line)     ; indirect y-indexed
           [(list _ num index more) (list (list (lex-number num)) (string->symbol index))]
           [_ (match (regexp-match #px"^[(](.*),[ \t]*([xXyY])[ \t]*[)](.*)$" line) ; indirect x/y-in
                [(list _ num index more) (list (list (lex-number num) (string->symbol index)))]
                [_ (match (regexp-match #px"^[(](.*)[)](.*)$" line)               ; indirect
                     [(list _ num more) (list (list (lex-number num)))]
                     [_ (match (regexp-match #px"^(.*),[ \t]*([xXyY])$" line)       ; indexed
                          [(list _ more index)
                           (list (lex-number (skip-whitespace more)) (string->symbol index))]
                          [_ (list (lex-number line))])])])])]))                  ; absolute
  (for/list ([line lines])
    (convert-line line)))

(define (split-string-into-lines text)
  (for/list ([line (in-lines (open-input-string text))])
    line))

;;;
;;; INITIALIZATION
;;;

(define (hexify n)     (number->string n 16))
(define (hexify* xs)   (map hexify xs))
(define (hexify** xss) (map hexify* xss))

(define (hexes->vector str)
  (define (hex x) (string->number x 16))
  (list->vector (map hex (string-split str " "))))

(define (install-program vec start-address)
  (for ([a (in-naturals start-address)]
        [v (in-vector vec)])
    (store a v)))

#;(begin

(assembler '((lda '10)
             (bne 20)
             (lda 30 x)
             (lda (40) y)))

  
(define test-program "a9 20 ff")
(hexes->vector test-program)
(install-program (hexes->vector test-program) 0)
; (run 0)

(traditional->assembler
   (split-string-into-lines
    "* = $400
     lda #$20
     bne $a
     lda foo,y
     lda ($54,x)
     ldx $54,y"))

(assembler
 (traditional->assembler
  (split-string-into-lines
    "* = $400
     LDA #$20   
     LDA   $20  
     LDA   $20,x
     LDX   $20,y
     LDA $1234  
     LDA $1234,x
     LDA $1234,y
     JMP ($1234)
     LDA ($44,x)
     LDA ($44),y
     BNE 20
     ROL A")))

(hexify**
   (rest
    (assembler
     (traditional->assembler
      (split-string-into-lines
       "* = $0
     LDA #$20   
     LDA   $20  
     LDA   $20,x
     LDX   $20,y
     LDA $1234  
     LDA $1234,x
     LDA $1234,y
     JMP ($1234)
     LDA ($44,x)
     LDA ($44),y
     BNE 20
     ROL A")))))

)

(define test06
  '((* = $600)
    (ROL A)
  
    (LDA '$6A)
    (STA $50)
    (LDA '$6B)
    (STA $51)
    (LDA '$A1)
    (STA $60)
    (LDA '$A2)
    (STA $61)
  
    (LDA '$FF)
    (ADC '$FF)
    (ADC '$FF)
    (SBC '$AE)
  
    (STA $40)
    (LDX $40)
    (ADC $00 X)
    (SBC $01 X)
  
    (ADC $60)
    (SBC $61)
  
    (STA $0120)
    (LDA '$4D)
    (STA $0121)
    (LDA '$23)
    (ADC $0120)
    (SBC $0121)
  
    (STA $F0)
    (LDX $F0)
    (LDA '$64)
    (STA $0124)
    (LDA '$62)
    (STA $0125)
    (LDA '$26)
    (ADC $0100 X)
    (SBC $0101 X)
  
    (STA $F1)
    (LDY $F1)
    (LDA '$E5)
    (STA $0128)
    (LDA '$E9)
    (STA $0129)
    (LDA '$34)
    (ADC $0100 Y)
    (SBC $0101 Y)
  
    (STA $F2)
    (LDX $F2)
    (LDA '$20)
    (STA $70)
    (LDA '$01)
    (STA $71)
    (LDA '$24)
    (STA $72)
    (LDA '$01)
    (STA $73)
    (ADC ($41 X))
    (SBC ($3F X))
  
    (STA $F3)
    (LDY $F3)
    (LDA '$DA)
    (STA $80)
    (LDA '$00)
    (STA $81)
    (LDA '$DC)
    (STA $82)
    (LDA '$00)
    (STA $83)
    (LDA '$AA)
    (ADC ($80) Y)
    (SBC ($82) Y)
    (STA $30)))

(define adc-test
  '((* = $600)
    (clc) 
    (lda '$f0)
    (adc '$07)
    (sta  $00)  ; C=0 expected $f7
    
    (sec) 
    (lda '$f0)
    (adc '$07)
    (sta  $01)  ; C=0 expected $f8

    (clc) 
    (lda '$f0)
    (adc '$20)
    (sta  $02)  ; C=1 expected $110 aka _10
    
    
    (sec) 
    (lda '$f0)
    (adc '$20)
    (sta  $03)  ; C=1 expected $111 aka _11

    (STOP)))
    


#;(begin (install-opcodes-from-assembler
        (assembler (append adc-test '((STOP)))))
       (run #x0600)
       (displayln (mem-dump 0)))

;;;
;;; ROM FILES
;;;

;; NES files are stored in the file format ines. The file extension is usually "nes".

(struct ines  (header               ; a header with more information
               trainer              ; 0 or 512 bytes
               prg-rom              ; 16384 * x bytes
               chr-rom              ; if present (8192 * y bytes
               playchoice-inst-rom  ; if present (0 or 8192 bytes
               playchoice-prom      ; if present (16 bytes Data)
               mirroring-type       ; 
               mapper)
  #:transparent)

(struct head (prg-rom-size chr-rom-size flag6 flag7 prg-ram-size flag9 flag10)
  #:transparent)

(define (read-ines-file path)
  (with-input-from-file path
    (λ() (read-ines))))

(define (read-ines [in (current-input-port)])
  (parameterize ([current-input-port in])
    ;; Header (16 bytes in total)
    ; 1. Tag: "NES^Z"
    (define header (read-bytes 16))
    (unless (equal? (subbytes header 0 3) #"NES")
      (displayln "Warning: rom files does not have NES header" (current-error-port)))
    ; 2. Size of PRG ROM in 16 KB Units
    (define prg-rom-size (* 16 1024 (bytes-ref header 4)))
    ; 3. Size of CHR ROM in  8 KB Units
    ; (If the size is 0, then the board uses CHR RAM)
    (define chr-rom-size (*  8 1024 (bytes-ref header 5)))
    ; 4. Flags 6 and 7
    (define flag6 (bytes-ref header 6))
    (define flag7 (bytes-ref header 7))
    ; 5. Size of PRG RAM in  8 KB Units
    (define prg-ram-size (* 8 1024 (bytes-ref header 8)))
    ; 6. Flags 9 and 10
    (define flag9  (bytes-ref header 10))
    (define flag10 (bytes-ref header 11))
    ; The remaining bytes of the header are zero-filled

    ;; Interpret flag 6
    (define mirroring-type       (if (bit-set? flag6 0) 'vertical 'horizontal))
    (define sram-at-6000-7fff    (bit-set? flag6 1))
    (define trainer?             (bit-set? flag6 2)) ; If yes, 512 byte trainer at 7000-71FF
    (define four-screen-mode?    (bit-set? flag6 3)) ; If yes, the M bit has no effect
    (define lower-4bit-of-mapper (bitlsr (bitlsr (bitlsr (bitlsr (byte-and flag6 #b11110000))))))

    ;; Interpret flag 7
    (define vs-system?           (bit-set? flag7 0))  ; arcade system
    (define playchoice?          (bit-set? flag7 1))  ; arcade system with two players
    (define nes-2.0-rules?       (and (bit-set? flag7 3) (bit-clear? flag7 2)))
    (define upper-4bit-of-mapper (byte-and flag7 #b11110000))

    ;; Mapper
    (define mapper (byte-or upper-4bit-of-mapper lower-4bit-of-mapper))
    
    ;; Trainer (0 or 512 bytes)
    (define trainer (if trainer? (read-bytes 512) #""))
    
    ;; PRG ROM
    (define prg-rom (read-bytes prg-rom-size))
    ;; CHR ROM
    (define chr-rom (read-bytes chr-rom-size))
    ;; PlayChoice 
    (define playchoice-inst-rom (and playchoice? (read-bytes 8192)))
    (define playchoice-prom     (and playchoice? (read-bytes 16)))

    (ines (head prg-rom-size chr-rom-size flag6 flag7 prg-ram-size flag9 flag10)
          trainer prg-rom chr-rom playchoice-inst-rom playchoice-prom
          mirroring-type mapper)))

(define (ines-human-info r)
  (define h (ines-header r))  
  (list 'prg-rom-size (head-prg-rom-size h)
        'prg-ram-size (head-prg-ram-size h)
        'chr-size     (head-chr-rom-size h)
        'mapper       (ines-mapper r)
        'mirroring    (ines-mirroring-type r)))
        
;;;
;;; INSTALLING THE ROM INTO MEMORY
;;;
; DK '(prg-rom-size 16384 prg-ram-size 0 chr-size 8192 mapper 0 mirroring horizontal)

(define (install-rom r)
  (define h        (ines-header  r))
  (define prg-size (head-prg-rom-size h))
  (define chr-size (head-chr-rom-size h))
  (define prg      (ines-prg-rom r))
  (define chr      (ines-chr-rom r))  ; this is to be installed in the PPU 
  (define mapper   (ines-mapper  r))
  ; $6000 - $7FFF Battery backed ram (size 2KB or $KB - mirrored to fill range)
  ; $8000 - $BFFF First 16KB of ROM
  ; $C000 - $FFFF Last  16KB of ROM (or mirror of first part)
  (displayln (list 'prg-size prg-size))
  (match mapper
    [0  (for ([a (in-naturals #x8000)]
              [b prg])                      ; install prg into $8000 - ...
          (store a b))
        (when (= prg-size (* 16 1024))                 ; mirror if prg is only 16KB
          (make-$C000-$FFFF-a-mirror-of-$8000-BFFF))
        (for ([a chr-size] [b chr])
          (ppustore a b))]))

;;;
;;; CHR ROM TO IMAGE
;;;

(define (make-half-row-cache)
  ;;; There are four different colors in a tile.
  ;;; The actual color is determined by the palette.
  ;;; For now just use four gray tones.
  (for/vector ([b (in-range 256)])
    ; The cache is indexed as:
    ;   (word nibble-from-bitplane0 nibble-from-bitplane1)
    ; Get the nibbles:
    (define u (byte-upper-nibble b))
    (define l (byte-lower-nibble b)) 
    ; Then combine bit pairs to get color number    
    (define (combine-bits l u i)
      (if (bit-set? l i)       ; lower bit
          (if (bit-set? u i)   ; upper bit
              3                ;   11
              1)               ;   01
          (if (bit-set? u i)   ; upper bit
              2                ;   10
              0)))             ;   00
    ;; Let's make a palette.
    (define (gray n) (bytes 255 n n n))
    (define palette  (vector (gray 0) (gray 85) (gray 170) (gray 255)))

    (bytes-append (vector-ref palette (combine-bits u l 3))
                  (vector-ref palette (combine-bits u l 2))
                  (vector-ref palette (combine-bits u l 1))
                  (vector-ref palette (combine-bits u l 0)))))

(define the-row-cache (make-half-row-cache))
(define (draw-tile cr n dc x y)
  ; draw tile number n from the chr-rom to the drawingcontext at position (x,y)
  (define start (* 16 n))   ; each tile is 16 bytes
  (define bp1 start)        ; bitplane 1 is stored in the first 8 bytes
  (define bp2 (+ start 8))  ; bitplace 2 is stored in the last  8 bytes
  (for ([i 8])      
    (define b0 (bytes-ref cr (+ bp1 i)))
    (define b1 (bytes-ref cr (+ bp2 i)))
    (define u0 (byte-upper-nibble b0))
    (define u1 (byte-upper-nibble b1))
    (define l0 (byte-lower-nibble b0))
    (define l1 (byte-lower-nibble b1))
    ;                           x    y w h 
    (send dc set-argb-pixels    x    (+ y i) 4 1 (vector-ref the-row-cache (nibbles->byte u0 u1)))
    (send dc set-argb-pixels (+ x 4) (+ y i) 4 1 (vector-ref the-row-cache (nibbles->byte l0 l1)))))

(define (chr-rom->image cr)
  ;; Each tile is stored using 16 bytes.
  (define size      (bytes-length cr))
  (define n-tiles (/ size 16))  
  (define bank-size (* 16 16 16)) ; 4096 bytes contains 16x16 tiles og size 8x8 pixels
  (define n-banks (/ size bank-size))
  (define bank-width  (* 16 8))
  (define bank-height (* 16 8))
  (displayln (list size n-tiles bank-size n-banks bank-width bank-height))
  ;; A pixel in a tile is represented as a 2 bit number.
  ;; The number is an index into a palette which holds the actual colors.
  ;; Make a bitmap large enough to contain all tiles
  (define rows (quotient n-tiles 8))
  (define cols 8)
  (define bm   (make-object bitmap% (* n-banks bank-width) bank-height))
  (displayln bm)
  (define dc    (new bitmap-dc% [bitmap bm]))
  (define cache (make-half-row-cache))
  (for ([bank n-banks])
    (for ([i 16])    ; row number
      (for ([j 16])  ; col number
        (define n (+ (* bank 256) (* i 16) j)) ; 16 tiles per row
        (define x (+ (* bank bank-width) (* j 8)))
        (define y (* i 8))
        (draw-tile cr n dc x y))))
  bm)

;;;
;;; PPU - Picture Processing Units
;;; 

; Reference: https://wiki.nesdev.com/w/index.php/PPU_registers

(define-syntax (define-ppu-register stx)
  (define-syntax-class access-type
    (pattern read)
    (pattern write)
    (pattern read/write)
    (pattern write-twice)
    (pattern read/write-increment))
  (define byte-masks         #(1 2 4 8 16 32 64 128))
  (define negated-byte-masks  (for/vector ([b byte-masks]) (- 255 b)))
  (define (bit-clear  b pos)  (bitwise-and b (vector-ref negated-byte-masks pos)))
  (define (bit-set    b pos)  (bitwise-ior b (vector-ref         byte-masks pos)))

  (syntax-parse stx #:datum-literals (access fields bits)
    [(_ name:id                                  ; name of register
        address:exact-nonnegative-integer        ; located at this memory address
        (access at:access-type)                  ; access type
        (fields (field-name:id from:exact-nonnegative-integer to:exact-nonnegative-integer) ...)
        (bits   (  bit-name:id index:exact-nonnegative-integer)                             ...))
     (with-syntax (; REGISTER NAME
                   [ppu-name              ; a variable holds the value of the ppu register
                    (format-id #'name "ppu-~a" #'name)]
                   [ppu-name-set!             ; store byte in register
                    (format-id #'name "ppu-~a-set!" #'name)]
                   ; FIELDS
                   [(ppu-field-name! ...) ; used to set bit fields to a given number
                    (format-ids #'(field-name ...) "ppu-~a-~a!" #'((name field-name) ...))]
                   [(ppu-field-name-set! ...) ; used to set bit fields to a given number
                    (format-ids #'(field-name ...) "ppu-~a-~a!" #'((name field-name) ...))]
                   [(ppu-field-name  ...) ; used to read  fields as a number
                    (format-ids #'(field-name ...) "ppu-~a-~a" #'((name field-name) ...))]
                   ; BITS
                   [(ppu-bit-name! ...)  ; used to set bit to 0 or 1
                    (format-ids #'(bit-name ...) "ppu-~a-~a!" #'((name bit-name) ...))]
                   [(ppu-bit-name-clear ...)  ; used to set bit to 0
                    (format-ids #'(bit-name ...) "ppu-~a-~a-clear" #'((name bit-name) ...))]
                   [(ppu-bit-name-set ...)  ; used to set bit to 1
                    (format-ids #'(bit-name ...) "ppu-~a-~a-set" #'((name bit-name) ...))]
                   [(ppu-bit-name  ...)  ; used to read the bit as 0 or 1
                    (format-ids #'(bit-name ...) "ppu-~a-~a" #'((name bit-name) ...))]
                   [(ppu-bit-name?  ...) ; used to read bit as a boolean
                    (format-ids #'(bit-name ...) "ppu-~a-~a?" #'((name bit-name) ...))]
                   ; Derived information
                   [reg-index             (- (syntax->datum #'address) #x2000)]
                   [(field-zero-mask ...) (for/list ([f (syntax->datum #'(from ...))]
                                                     [t (syntax->datum #'(to   ...))])
                                            (for/fold ([mask #x11111111]) ([i (in-range f (+ t 1))])
                                              (bit-clear mask i)))]
                   [(field-one-mask ...)  (for/list ([f (syntax->datum #'(from ...))]
                                                     [t (syntax->datum #'(to   ...))])
                                            (for/fold ([mask 0]) ([i (in-range f (+ t 1))])
                                              (bit-set mask i)))])
     (syntax/loc stx
       (begin
         ; REGISTER
         (define (ppu-name)        (ppu-reg-ref  reg-index))
         (define (ppu-name-set! b) (ppu-reg-set! reg-index b))
         ; FIELDS
         (begin
           ; TODO fix writing to fields
           (define (ppu-field-name-set! v) (bitwise-ior (bitwise-and (ppu-name) field-zero-mask)
                                                        (byte<< v from)))
           (define (ppu-field-name)        (byte>> (bitwise-and (ppu-name) field-one-mask) from)))
         ...
         ; BITS
         (begin           
           (define (ppu-bit-name-clear)   (ppu-reg-set! reg-index (bit-clear (ppu-name) index)))
           (define (ppu-bit-name-set)     (ppu-reg-set! reg-index (bit-set   (ppu-name) index)))
           (define (ppu-bit-name?)            (bit-set? (ppu-name) index))
           (define (ppu-bit-name)         (if (bit-set? (ppu-name) index) 1 0)))
         ...)))]))
 
(define-ppu-register ctrl #x2000
  (access write)
  (fields (N 0 1))                      ; nametable select (two bit)
  (bits   (I 2)                         ; increment mode
          (S 3)                         ; sprite tile select
          (B 4)                         ; background tile select
          (H 5)                         ; sprite height
          (P 6)                         ; PPU master/slave
          (V 7)))                       ; NMI Enable
(define (base-nametable-address)           (+ #x2000 (* (ppu-ctrl-N) #x400)))
(define (vram-address-increment)           (if (ppu-ctrl-I?) 32 1)) ; corresponds to down or right
(define (sprite-pattern-table-address)     (if (ppu-ctrl-S?) #x1000 #x0000)) ; for 8x8 sprites
(define (background-pattern-table-address) (if (ppu-ctrl-B?) #x1000 #x0000))
(define (sprite-height)                    (if (ppu-ctrl-H?) 16 8)) ; width is always 8
(define (generate-nmi-at-start-of-vblank?) (ppu-ctrl-V?))

(define-ppu-register mask      #x2001
  (access write)
  (fields)
  (bits (g 0)                          ; grey scale
        (m 1)                          ; background left column enable
        (M 2)                          ; sprite     left column enable
        (b 3)                          ; background             enable
        (s 4)                          ; sprite                 enable
        (R 5)                          ; color emphasis
        (G 6)                          ; color emphasis
        (B 7)))                        ; color emphasis

(define (greyscale?)                             (ppu-mask-g?))
(define (show-background-in-8-left-most-pixels?) (ppu-mask-m?))
(define (show-sprites-in-8-left-most-pixels?)    (ppu-mask-M?))
(define (show-background?)                       (ppu-mask-b?))
(define (show-sprites?)                          (ppu-mask-s?))

(define (emphasize-red?)    (case video-type [(ntsc) (ppu-mask-R?)] [(pal) (ppu-mask-G?)]))
(define (emphasize-green?)  (case video-type [(ntsc) (ppu-mask-G?)] [(pal) (ppu-mask-R?)]))
(define (emphasize-blue?)                            (ppu-mask-B?))

(define-ppu-register status    #x2002
  (access read)
  (fields)
  ; Reading bits 0,1,2,3,4 gets bits from the last value on the PPU bus (see "latch" below).
  (bits (O 5)                          ; sprite overflow, read resets write pair for $2005/$2006  ?
        (S 6)                          ; sprite 0 hit
        (V 7)))                        ; vblank (0: not in vblank, 1: in vblank)
(define (sprite-overflow?) (ppu-status-O?)) ; see explanation on sprites
(define (sprite0-hit?)     (ppu-status-S?)) ; see explanation on sprites
(define (vertical-blank?)  (ppu-status-V?)) ; on during vertical blanking

(define-ppu-register oam-addr  #x2003  ; oam read/write address
  (access write)            ; write twice with msb then lsb to set the address
  (fields (a 0 7)) (bits))

(define-ppu-register oam-data  #x2004  ; oam read/write data
  (access read/write-increment)        ; Note: writes will increment the address register
  (fields (d 0 7)) (bits))

(define-ppu-register scroll    #x2005  ; fine scroll position (two writes X, Y)
  (access write-twice)
  (fields (x 0 7)) (bits))

;; The PPU register ADDR needs special handling.
#;(define-ppu-register addr      #x2006  ; PPU read/write address (two writes: MSB, LSB)
    (access write-twice) (fields (a 0 7)) (bits))
(define ppu-addr-first-write?  #f)   ; first (of two) writes to ppu-addr ?
(define ppu-addr-current        0)   ; current address
(define (ppu-addr-read)         ppu-addr-current) ; read
(define (ppu-addr-write b)       ; write
  (set! ppu-addr-current      (if ppu-addr-first-write?
                                  (word (word-msb  ppu-addr-current) b)
                                  (word b (word-lsb ppu-addr-current))))
  #;(unless ppu-addr-first-write?
      (displayln (list 'ppu-addr-write ppu-addr-current) (current-error-port)))
  (set! ppu-addr-first-write? (not ppu-addr-first-write?)))

;; The PPU register DATA also needs special handling.
#;(define-ppu-register data      #x2007  ; PPU data read/write
    (access read/write) (fields (d 0 7)) (bits))

(define (ppu-data-write b)
  (ppustore ppu-addr-current b)
  (set! ppu-addr-current (+ ppu-addr-current (if (ppu-ctrl-I?) 32 1))))

(define-ppu-register oam-dma   #x4014  ; OAM DMA high address
  (access write)
  (fields (a 0 7)) (bits))             ; TODO: hook up in load / store

;;;
;;; PPU Stepping
;;;

; Reference: http://nesdev.icequake.net/PPU.txt

(define ppu-scan-line     0)
(define ppu-current-cycle 0)
(define ppu-step
  ; one scan line is 1364 ppu cycles (which is 1364/12 = 113+2/3 cpu cycles)
  ; one frame is 357368 cycles = 262 scanlines
  (let ()
    
    (define state        0) ; current state of the PPU
    (define left         1) ; number of cycles remaining to stay in the current state
    (define even-frame? #t) ; alternates between #f and #t
    (define line         0) ; current scan line (counted from first visible line)

    
    ;; START OF FRAME
    ; these numbers does not match the code below
    ; 0. put vblank down (and generate nmi)    <---!!!
    ; 1. wait 20 scan lines
    ; 2. 1 dummy scan line (alternates between 1360 and 1364 cycles)
    ; 3. 240 rendered scan lines
    ; 4. 1 wait one scan line
    ; 5. set vblank up
    
    (λ (cycles)
      (let loop ([cycles cycles]) ; cycles to spend
        (cond
          ; 0. Start of frame
          [(= state 0)                    ; (display "START FRAME" (current-error-port))
                                          (set! even-frame? (not even-frame?))
                                          (ppu-status-V-set) ; vblank starts
                                          (set! nmi-due-to-vblank? #t) ; signal NMI to cpu
                                          (send c on-paint)
                                          (set! state 1)
                                          (set! left (* 20 1364)) ; 20 lines, 1364 cycles each
                                          (loop cycles)]
          ; 1. Wait 20 scan lines
          [(= state 1) ;(display "1")
                       (cond
                         ;; yield to cpu?
                         [(< cycles left) (set! left (- left cycles))]
                         ;; waiting over
                         [else            (define new-cycles (- cycles left))    ; use left cycles
                                          (ppu-status-V-set)                     ; vblank stops
                                          (set! state 2)                         ; next state
                                          (set! left (if even-frame? 1364 1360)) ; dummy scan line
                                          (loop new-cycles)])]
          ; 2. Dummy scan line. Alternates betwen 1364 and 1360 cycles
          [(= state 2) ;(display "2")
                       (cond
                         ;; yield to cpu?
                         [(< cycles left) (set! left (- left cycles))]          ; use available cycles
                         ;; ready for rendering
                         [else            (define new-cycles (- cycles left))   ; use left cycles
                                          (set! state 3)
                                          (set! left 1364)
                                          (set! line 0)                         ; next line is first
                                          (render-line dc 0)                    ; visible line
                                          (loop new-cycles)])]
          ; 3. Render one line at a time. Each lines is 1364 cycles.
          [(= state 3) ;(display "3")
                       (cond
                         ;; yield to cpu?
                         [(< cycles left) (set! left (- left cycles))]          ; use available cycles
                         ;; stay in state 3 (more lines to render)
                         [(< line 240)    (define new-cycles (- cycles left))   ; use left cycles
                                          (set! line (+ line 1))
                                          (render-line dc line)
                                          (set! left 1364)
                                          (loop new-cycles)]
                         ; ready for next state
                         [else            (define new-cycles (- cycles left))   ; use left cycles
                                          (set! state 4)
                                          (set! left 1364)
                                          (loop new-cycles)])]
          ; 4. Wait one scan line.
          [(= state 4) ;(display "4")
                       (cond
                         ;; yield to cpu?
                         [(< cycles left) (set! left (- left cycles))]          ; use available cycles
                         ;; 
                         [else            (define new-cycles (- cycles left))
                                          (set! state 0)
                                          (loop new-cycles)])]
          [else (error)])))))
                 

;;;
;;; PPU Tiles
;;;

; A screen consists of 32x30 (= 960) tiles.
; For each tile a byte is stored in a name table.

; SYNTAX (in-tiles a)
;   The sequence syntax (in-tiles a) will generate a sequence of
;   the 960 bytes in the nametable starting at address a.
(define-sequence-syntax in-tiles
  (lambda () #'in-tiles/proc)
  (lambda (stx)
    (syntax-parse stx
      [[(b) (_in-tiles start-address)]
       (syntax/loc stx
         [(b) (:do-in ([(start)    start-address]
                       [(stop)  (+ start-address 960)])
                      (integer? start)
                      ([i start])
                      (< i stop)
                      ([(b) (ppuload i)])
                      #t
                      #t
                      [(+ i 1)])])])))
(define (in-tiles/proc) (error 'in-tiles/proc))


; The 32x30 tiles can be divided into blocks of 2x2 tiles.
; This gives 16x16 blocks. The attribute table holds 2 bits
; per block indicating which palette is used in the block.

; Consider the first four tile rows:

;    t00 t01  t02 t03  ... t30 t31   ; 32 tiles in a row
;    t32 t33  t34 t53  ... t62 t63

;    t64 t65  t66 t67  ...   ...  
;    t96 t97  t98 t99  ...   ...

; If we look at the block arrangement we get:

;    b3       b2       b7    b6   ...  b15 b14
;    b1       b0       b5    b4   ...  b13 b12

; The four bit pairs from block b0, b1, b2, and, b3 are stored in a single byte:

;    bit position  76 54 32 10
;    block          0  1  2  3

; That is if we have the attributes in the attribute table:
;    a0, a1, a2, a3, ...
; then we need need to check whether we are on an even or an odd tile row number.
; On even rows (say row 0) we need to deliver the lower four bits.
; On odd  rows (say row 1) we need to deliver the upper four bits.
; Of the four bits, the lower two bits are used first, then following two bits.
; However the bits are used twice since the block width is two tiles.

; The 32x30 tiles are 16x15 blocks. With 2 bits per block, we can store
; attributes for 4 blocks in each byte. This gives 16x15/4 = 60 bytes.
; However, the size of the attribute table is 64 bytes.

; SYNTAX (in-attributes a)
;   The sequence syntax (in-tiles a) will generate a sequence of 2 bits numbers.
;   The 2 bit numbers represent a palette.
;   The sequences (in-tiles a) and (in-attributes a) can be used in parallel.
(define-sequence-syntax in-attributes
  (lambda () #'in-attributes/proc)
  (lambda (stx)
    (syntax-parse stx
      [[(a) (_in-attributes attribute-table scan-line)]
       (syntax/loc stx
         [(a) (:do-in ([(tile-row)  (quotient scan-line 8)]
                       [(block-row) (quotient scan-line 16)]
                       [(start)     (+ attribute-table (* 8 (quotient scan-line 16)))])
                      (and (integer? attribute-table) (integer? scan-line))
                      ([c               0]                      ; tile column
                       [r               tile-row])              ; tile row
                      (< r 30)
                      ([(a) (let* ([j (+ attribute-table (* 8 (quotient r 4)) (quotient c 4))]
                                   [b (ppuload j)]
                                   [n (if (even? (quotient r 2))      ;        even  odd
                                          (byte-lower-nibble b)       ;  even:  10    32
                                          (byte-upper-nibble b))])    ;  odd:   54    76
                              
                              (if (even? (quotient c 2))
                                  (byte-and (byte>> n 2) #b11)
                                  (byte-and         n    #b11)))])
                      #t
                      #t
                      [(if (= c 31)    0    (+ c 1)) ; 32 tile columns in total
                       (if (= c 31) (+ r 1) r)])])])))
(define (in-attributes/proc) (error 'in-attributes/proc))

; The PPU bus works as a latch.
;   "Latch" a circuit which retains whatever output state results from a momentary input signal
;   until reset by another signal.
; Reading and writing to the PPU bus will fill the latch. I.e. the values stay on the bus.

; Rendering the background:
;   A nametable contains tile numbers.
;   There are 32 tiles in a row.
;   The tile bitmap is stored in chr rom.
;   Only two bits pr pixel is stored in the tile bitmap.
;   The two bits are used as an index into a palette (each palette consists of four colors).
;   The attribute table has two bits for each block (16x16 pixels) and determines
;   for each block which which palette is used.
;
; The native rendering algorithm becomes.
;    For each pixel:
;      1. Look up current palette in the attribute table.
;      2. Look up the tile number in the nametable.
;      3. Use the tile number to find the tile bitmap in chr rom,
;         and use the palette to decode the tile.

; The following list of rgb values are from  https://wiki.nesdev.com/w/index.php/PPU_palettes
; Note: The eight blacks are missing from the linked to table.
(define colors-as-rgb
  #(#( 84  84  84) #(  0  30 116) #(  8  16 144) #( 48   0 136)
    #( 68   0 100) #( 92   0  48) #( 84   4   0) #( 60  24   0)
    #( 32  42   0) #(  8  58   0) #(  0  64   0) #(  0  60   0)
    #(  0  50  60) #(  0   0   0) #(  0   0   0) #(  0   0   0)

    #(152 150 152) #(  8  76 196) #( 48  50 236) #( 92  30 228)
    #(136  20 176) #(160  20 100) #(152  34  32) #(120  60   0)
    #( 84  90   0) #( 40 114   0) #(  8 124   0) #(  0 118  40)
    #(  0 102 120) #(  0   0   0) #(236 238 236) #(76  154 236)
    #(120 124 236) #(176  98 236) #(  0   0   0) #(  0   0   0)

    #(228  84 236) #(236  88 180) #(236 106 100) #(212 136  32)
    #(160 170   0) #(116 196   0) #( 76 208  32) #( 56 204 108)
    #( 56 180 204) #( 60  60  60) #(236 238 236) #(168 204 236)
    #(188 188 236) #(212 178 236) #(  0   0   0) #(  0   0   0)

    #(236 174 236) #(236 174 212) #(236 180 176) #(228 196 144)
    #(204 210 120) #(180 222 120) #(168 226 144) #(152 226 180)
    #(160 214 228) #(160 162 160) #(  0   0   0) #(  0   0   0)))

(define color-objects
  (for/vector ([rgb colors-as-rgb])
    (match rgb [(vector r g b) (make-object color% r g b)])))
(define (color->color% c) (vector-ref color-objects c))

(define screen-buffer (make-bytes (* 4 256 240))) ; 4 bytes for each pixel
(define (plot-pixel/screen-buffer x y c)
  (unless (>= y 240) ; skip the dummy line
    (define i (+ (* (* 4 256) y) (* 4 x)))
    (define rgb (if (< c (vector-length colors-as-rgb))
                    (vector-ref colors-as-rgb c)
                    #(255 0 0)))
    (displayln (list x y i c))
    (bytes-set! screen-buffer    i    255)                 ; α = 255 means non-transparent
    (bytes-set! screen-buffer (+ i 1) (vector-ref rgb 0))
    (bytes-set! screen-buffer (+ i 2) (vector-ref rgb 1))
    (bytes-set! screen-buffer (+ i 3) (vector-ref rgb 2))))
(define (render-screen-from-buffer dc)
  ;(displayln "SCREEN UPDATE" (current-error-port))
  (send dc set-argb-pixels 0 0 256 240 screen-buffer))

#;(define line-buffer (make-bytes (* 4 256)))
#;(define (plot-pixel/line-buffer x c)
  (define i (* 4 x))
  (define rgb (vector-ref colors-as-rgb c))
  (bytes-set! line-buffer    i    255)                 ; α = 255 means non-transparent
  (bytes-set! line-buffer (+ i 1) (vector-ref rgb 0))
  (bytes-set! line-buffer (+ i 2) (vector-ref rgb 1))
  (bytes-set! line-buffer (+ i 3) (vector-ref rgb 2)))
#;(define (render-line-from-buffer dc y)
  (send dc set-argb-pixels 0 y 256 1 line-buffer))

(define (render-line dc y)
  (define pattern-table   (background-pattern-table-address)) ; stores the tile bitmaps
  (define name-table      (base-nametable-address))           ; stores the tile numbers
  ;                                                           ; ( ppu-ctrl-N picks 1 of 4 tables )
  (define name-table-size (* 32 30)) ; = $03c0
  (define attribute-table (+ name-table name-table-size)) ; the attribute table follows the name-table
  
  ; 32x30 tiles, or 256x240 pixels (Note: 8*32 = 256  and 8*30=240.)
  ; For each position the nametable has a byte with the tile number.
  (define rows-done  (byte>> y 3))      ; divide by 8 to find the number of tile rows already done
  (define start-tile (* 32 rows-done))  ; each of the previous rows is 32 tiles wide

  (define ∆y (remainder y 8))  ; 0 <= ∆y < 8
  (for ([tile      (in-tiles      (+ name-table start-tile))] ; index into the pattern   table
        [attribute (in-attributes attribute-table y)]         ; two bit attribute (repeated twice)
        [n         (in-range start-tile (+ start-tile 32))]) ; 32 tiles on a line      
    ; 1. Background palettes from $3F00 and sprite palettes from $3F10.
    ;    https://wiki.nesdev.com/w/index.php/PPU_palettes
    ;    Each palette has four colors - but due to mirroring
    ;    the first color of each palette are shared by all palettes.
    ;    In hardware it is done by mirroring $3F00, $3F04 , $3F08, $3F0C
    ;    and likewise -
    ;    TODO wording is wrong. There is no mirroring, but rendering uses the universal color.
    ; The pattern starts at address  pattern-table  but we need to adjust for y    
    ; Each pattern is 16 bytes. It has two bitplanes, so we need by ∆y and ∆y+8.    
    (define pat0 (ppuload (+ pattern-table (* 16 tile)   ∆y)))
    (define pat1 (ppuload (+ pattern-table (* 16 tile) 8 ∆y)))
    (for ([i (in-range 0 8)]) ; for each pixel in the tile
      ; TODO: switched the bit order here ... WHY?
      (define pixel-from-tile  (byte-or (byte<< (bit-ref pat1 (- 7 i)) 1)
                                        (bit-ref pat0 (- 7 i))))
      (define palette-index    (byte-or (byte<< attribute 2) pixel-from-tile))
      ; (displayln (list 'palette-index palette-index) (current-error-port))
      (define color            (ppuload (+ #x3F00 palette-index 0))) ; mirror => #3F00
      ; (displayln (list 'color color))
      (define tile-row-start-x (remainder n 32))  ; 32 tiles on a row
      (define x                (+ (* 8 tile-row-start-x) i))
      (plot-pixel/screen-buffer x y color)))
  (when (= y 239)
    (render-screen-from-buffer dc)))
      ;(define universal-background-color (ppuload (+ #x3F00 palette-index 0))) ; mirror => #3F00
      ;(define color1                     (ppuload (+ #x3F00 palette-index 1)))
      ;(define color2                     (ppuload (+ #x3F00 palette-index 2)))
      ;(define color3                     (ppuload (+ #x3F00 palette-index 3)))
  
;;;
;;; EXAMPLE
;;;

; Donkey Kong (World) (Rev A) - mapper 0
(define (read-donkey-kong-rom)  (read-ines-file "roms/dk.nes"))
(define (read-background-rom)   (read-ines-file "roms/background.nes"))
(define (read-gauntlet-rom)     (read-ines-file "roms/Gauntlet.nes"))
(define (read-balloon-fight-rom) (read-ines-file "roms/Balloon Fight.nes"))
(define (read-baseball-rom) (read-ines-file "roms/Baseball.nes"))
(define (read-mario-bros-rom) (read-ines-file "roms/Mario Bros.nes"))
(define (read-millipede-rom) (read-ines-file "roms/Millipede.nes"))

;;; Uncomment to try
(require pict)

#;(

(define dk-rom (read-donkey-kong-rom))
(define bg-rom (read-background-rom))
(define gt-rom (read-gauntlet-rom))
(define bf-rom (read-balloon-fight-rom))
(define bb-rom (read-baseball-rom))
(define mb-rom (read-mario-bros-rom))
(define mm-rom (read-millipede-rom))

(scale (bitmap (chr-rom->image (ines-chr-rom dk-rom))) 3)
(ines-mapper dk-rom)
(ines-mirroring-type dk-rom)
(install-rom dk-rom)
;(install-rom bg-rom)
;(install-rom gt-rom)
; (install-rom bf-rom)
; (install-rom bb-rom)
;(install-rom mm-rom)
)

(define (plot-pixel dc x y color)
  (send dc set-pen (color->color% color) 1 'solid)
  (send dc draw-point x y))

(define (draw-background)
  (define bm   (make-object bitmap% (* 32 8) (* 30 8)))
  (define dc   (new bitmap-dc% [bitmap bm]))
  (for ([y (in-range 0 (* 30 8))])
    (render-line dc y)))

(require racket/gui/base)
(define bm (make-bitmap (* 32 8) (* 30 8)))
(define dc (new bitmap-dc% [bitmap bm]))
(define f  (new frame%  [label "racket-nes"]))
(define c  (new canvas% [parent f] [min-width 400] [min-height 400]
                [paint-callback (λ (c dc) (send dc draw-bitmap bm 0 0))]))
(send f show #t)

(reset)   ; soft reset sets PC to reset vector
(define the-process (thread (λ () (with-output-to-file "/users/soegaard/log.txt"
                                    (λ () (trace 1000000) (run PC))
                                    #:exists 'replace))))
(define (suspend) (thread-suspend the-process))
(define (resume)  (thread-resume  the-process))
; (thread (λ () (run PC)))
'done

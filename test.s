ld HL, $A ; address 10
rst $28   ; reset (jumps to $28 anyways lmao)
dw $450A  ; puts
; rst $28 + dw whatever == bcall (TI 83+ random thingimajiger made by TI)
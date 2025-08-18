macro bcall label
rst $28
dw arg:label
endmacro

bcall $450A
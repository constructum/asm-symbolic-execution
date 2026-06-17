asm binary_search

// // the next 'import' statement is not needed for asm-symbolic-execution (but is needed for ASMETA)
// import ../STDL/StandardLibrary

signature:
    controlled n : Integer
    controlled a : Integer -> Integer
    controlled x : Integer
    controlled l : Integer
    controlled r : Integer
    controlled pos : Integer

    derived sorted          : Boolean
    derived element_present : Boolean
    derived terminated      : Boolean


definitions:
    function sorted = (forall $k in {0:(n-2)} with a($k) <= a($k+1))
    function element_present = (exist $k in {0:(n-1)} with a($k) = x)
    function terminated = not (l <= r and pos = -1)

	invariant inv over pos : ((sorted and terminated) implies (if element_present then a(pos) = x else pos = -1 endif))

    main rule r_Main =
        if l <= r and pos = -1 then
            let ($m = (l + r) div 2) in
                if a($m) = x then
                    pos := $m
                else
                    if a($m) > x
                    then r := $m - 1
                    else l := $m + 1
                    endif
                endif
            endlet
        endif


default init n4:
    function n = 4
    function l = 0
    function r = 3      // = n - 1
    function pos = -1

init n1:
    function n = 1
    function l = 0
    function r = 0      // = n - 1
    function pos = -1

init n2:
    function n = 2
    function l = 0
    function r = 1      // = n - 1
    function pos = -1

init n3:
    function n = 3
    function l = 0
    function r = 2      // = n - 1
    function pos = -1

init n5:
    function n = 5
    function l = 0
    function r = 4      // = n - 1
    function pos = -1

init n6:
    function n = 6
    function l = 0
    function r = 5      // = n - 1
    function pos = -1

init n7:
    function n = 7
    function l = 0
    function r = 6      // = n - 1
    function pos = -1

init n8:
    function n = 8
    function l = 0
    function r = 7      // = n - 1
    function pos = -1

init n9:
    function n = 9
    function l = 0
    function r = 8      // = n - 1
    function pos = -1

init n10:
    function n = 10
    function l = 0
    function r = 9      // = n - 1
    function pos = -1


/*
    // some initialisation for a concrete, i.e. non-symbolic, run
    // (to be commented out for symbolic execution)
    function a($i in Integer) =
        switch $i
            case 0 : 2
            case 1 : 5
            case 2 : 7
            case 3 : 13
            case 4 : 18
            case 5 : 25
            case 6 : 27
            case 7 : 30
            case 8 : 35
            case 9 : 41
            otherwise 50
        endswitch
*/

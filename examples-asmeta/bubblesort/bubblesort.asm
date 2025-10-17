asm bubblesort

import ../STDL/StandardLibrary


signature:
    controlled n : Integer              // 'n' must be static for option '-turbo2basic'; this works for '-steps 1' though
    controlled ii : Integer
    controlled j : Integer
    controlled a : Integer -> Integer
    controlled sorted : Boolean


definitions:
//    function n = 3                   // if 'n' were to be static, it would have to be defined here

    main rule r_Main = seq
        //--- sorting algorithm
        ii := 0
        while (ii < n) do seq
            j := n - 1
            while (j > ii) do seq
                if a(j-1) > a(j)
                then par a(j-1):=a(j) a(j):=a(j-1) endpar 
                endif
                j := j - 1
            endseq
            ii := ii + 1
        endseq
        //--- verification that the array is sorted
        par
            sorted := true
            ii := 0
        endpar
        while (ii < n - 1) do par
            sorted := sorted and (a(ii) <= a (ii+1))
            ii := ii + 1
        endpar
    endseq


default init n3:
    function n = 3


// other initial state options for testing


init n1: function n = 1
init n2: function n = 2

init n4: function n = 4
init n5: function n = 5
init n6: function n = 6
init n7: function n = 7
init n8: function n = 8
init n9: function n = 9
init n10: function n = 10


/*
// some initialization for the simulator, to be commented out for symbolic execution

default init s0:
    function a($i in Integer) =
        switch $i
            case 0 : 5
            case 1 : 3
            case 2 : 2
            case 3 : 7
            case 4 : 4
            case 5 : 1
            case 6 : 9
            case 7 : 8
            case 8 : 0
            case 9 : 6
        endswitch
*/

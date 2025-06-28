asm matrixmult

import ../STDL/StandardLibrary


signature:
    controlled m : Integer              // 'm' must be static for option '-turbo2basic'; this works for '-steps 1' though
    controlled n : Integer              // 'n' must be static for option '-turbo2basic'; this works for '-steps 1' though
    controlled p : Integer              // 'p' must be static for option '-turbo2basic'; this works for '-steps 1' though
    controlled a : Prod(Integer, Integer) -> Integer
    controlled b : Prod(Integer, Integer) -> Integer
    controlled c : Prod(Integer, Integer) -> Integer
    controlled ii : Integer
    controlled j : Integer
    controlled k : Integer
    

definitions:
    // function m = 2                   // if 'm' were to be static, it would have to be defined here
    // function n = 3                   // if 'n' were to be static, it would have to be defined here
    // function p = 4                   // if 'p' were to be static, it would have to be defined here

    main rule r_Main =
        seq
            ii := 1
            while (ii <= m) do seq
                j := 1
                while (j <= p) do seq
                    par
                        c(ii, j) := 0
                        k := 1
                    endpar
                    while (k <= n) do par
                        c (ii, j) := c (ii, j) + a (ii, k) * b (k, j)
                        k := k + 1
                    endpar
                    j := j + 1
                endseq
                ii := ii + 1
            endseq
        endseq


default init mnp_2_3_4:
    function m = 2
    function n = 3
    function p = 4

init mnp_2_2_2:
    function m = 2
    function n = 2
    function p = 2

init mnp_3_3_3:
    function m = 3
    function n = 3
    function p = 3

init mnp_4_4_4:
    function m = 4
    function n = 4
    function p = 4



/*
// some initialization for the simulator, to be commented out for symbolic execution

default init s0:
    function a($i in Integer, $j in Integer) =
        switch ($i, $j)
            case (1, 1) : 1
            case (1, 2) : 2
            case (1, 3) : 3
            case (2, 1) : 4
            case (2, 2) : 5
            case (2, 3) : 6
        endswitch
    function b($i in Integer, $j in Integer) =
        switch ($i, $j)
            case (1, 1) : 1
            case (1, 2) : 2
            case (1, 3) : 3
            case (1, 4) : 4
            case (2, 1) : 5
            case (2, 2) : 6
            case (2, 3) : 7
            case (2, 4) : 8
            case (3, 1) : 9
            case (3, 2) : 10
            case (3, 3) : 11
            case (3, 4) : 12
        endswitch
*/

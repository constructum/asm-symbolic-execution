asm bubblesort

signature:
    domain Size subsetof Integer
    controlled n : Size
    controlled j : Integer
    controlled k : Integer
    controlled a : Integer -> Integer
    controlled terminated : Boolean

definitions:
    domain Size = { 1 : 6 }

    invariant ordered_after_execution over a :
        terminated implies
            (forall $i in { 0 : n-2 } with a($i) <= a($i+1))

    main rule r_Main =
        if not (terminated) then seq
            j := 0
            while (j < n) do seq
                k := n - 1
                while (k > j) do seq
                    if a(k-1) > a(k)
                    then par a(k-1):=a(k) a(k):=a(k-1) endpar 
                    endif
                    k := k - 1
                endseq
                j := j + 1
            endseq
            terminated := true
        endseq endif


// initial states to verify specific sizes

default init n3:
    function n = 3
    function terminated = false

init n5:
    function n = 5
    function terminated = false

init n6:
    function n = 6
    function terminated = false


// initial to test all size in domain Size at ones
init all:
    function terminated = false


// initial state with concrete values for non-symbolic execution

init non_symbolic:
    function n = 5
    function terminated = false
    function a($i in Integer) =
        switch $i
            case 0 : 5
            case 1 : 3
            case 2 : 4
            case 3 : 1
            case 4 : 2
            otherwise 0
        endswitch

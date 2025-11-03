asm bubblesort_with_invariant


signature:
    domain Size subsetof Integer
    controlled n : Size
    controlled j : Integer
    controlled k : Integer
    controlled a : Integer -> Integer
    controlled terminated : Boolean


definitions:
    domain Size = { 1 : 10 }

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


// initialization to verify specific sizes
init n1:
    function n = 1
    function terminated = false

init n2:
    function n = 2
    function terminated = false

default init n3:
    function n = 3
    function terminated = false

init n4:
    function n = 4
    function terminated = false

init n5:
    function n = 5
    function terminated = false

init n6:
    function n = 6
    function terminated = false

init n7:
    function n = 7
    function terminated = false

init n8:
    function n = 8
    function terminated = false

init n9:
    function n = 9
    function terminated = false

init n10:
    function n = 10
    function terminated = false


// initialization with concrete initial values for non-symbolic execution
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

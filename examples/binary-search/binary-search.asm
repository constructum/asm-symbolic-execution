function a : Integer -> Integer

function l : Integer
function m : Integer
function r : Integer

function x : Integer
function pos : Integer

function i : Integer
function sorted : Boolean
function includes_x : Boolean
function correct : Boolean


rule Main = [

    // check that array is sorted (precondition)
    { sorted := true, i := 0 };
    while (i < n - 1) { sorted := sorted and (a(i) <= a (i+1)), i := i + 1 };

    if sorted then [

        { l := 0, r := n - 1 };
        pos := -1;
        while (l <= r and pos = -1) [
            m := (l + r) div 2;
            if a(m) = x
            then pos := m
            else if a(m) < x
                 then l := m + 1
                 else r := m - 1
                 endif
            endif
        ];

        // check that result is correct (postcondition)
        { includes_x := false, i := 0 };
        while (i <= n - 1) { includes_x := includes_x or a(i) = x, i := i + 1 };
        correct := if includes_x
                   then pos >= 0 and pos < n and a(pos) = x
                   else pos = -1 endif

    ] endif

]




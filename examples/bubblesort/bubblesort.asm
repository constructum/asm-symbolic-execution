function i : Integer
function j : Integer
function a : Integer -> Integer
function sorted : Boolean


rule Main = [
    i := 0;
    while (i < n) [
        j := n - 1;
        while (j > i) [
            if a(j-1) > a(j)
            then { a(j-1) := a(j), a(j) := a(j-1) } endif;
            j := j - 1
        ];
        i := i + 1
    ];

    { sorted := true, i := 0 };
    while (i < n - 1) { sorted := sorted and (a(i) <= a (i+1)), i := i + 1 }
]

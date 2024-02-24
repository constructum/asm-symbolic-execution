function a : Integer, Integer -> Integer
function b : Integer, Integer -> Integer
function c : Integer, Integer -> Integer
function i : Integer
function j : Integer
function k : Integer


rule Main = [
    i := 1;
    while (i <= m) [
        j := 1;
        while (j <= p) [
            { c (i, j) := 0, k := 1 };
            while (k <= n) {
                c (i, j) := c (i, j) + a (i, k) * b (k, j),
                k := k + 1
            };
            j := j + 1
        ];
        i := i + 1
    ]
]

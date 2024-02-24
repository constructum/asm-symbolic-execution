//
// ASM translation of a public domain non-recursive C implementation
// of quicksort by Darel Lex Finley found at
// https://alienryderflex.com/quicksort/
// (version B, taking measures to limit the growth of the stack)
//
// Web archive URL:
// http://web.archive.org/web/20231011123155/http://alienryderflex.com/quicksort/
//

function a : Integer -> Integer     // elements
function beg_ : Integer -> Integer  // "beginning of partition" stack
function end_ : Integer -> Integer  // "end of partition" stack
function i    : Integer             // stack pointer, later reused for sortedness check loop

function piv : Integer              // pivot

function l : Integer                // leftmost index of current partition
function r : Integer                // rightmost index of current partition

function sorted : Boolean           // used for sortedness check at the end


rule Main = [
    i := 0;
    { beg_(i) := 0, end_(i) := n };
    while (i >= 0) [
        { l := beg_(i), r := end_(i) - 1 };
        if l < r then [
            piv := a(l);
            while (l < r) [
                while (a(r) >= piv and l < r) r := r - 1;
                if l < r then { a(l) := a(r), l := l + 1 } endif;
                while (a(l) <= piv and l < r) l := l + 1;
                if l < r then { a(r) := a(l), r := r - 1 } endif
            ];
            { a(l) := piv, beg_(i + 1) := l + 1, end_(i + 1) := end_(i), end_(i) := l };
            i := i + 1;
            if (end_(i) - beg_(i) > end_(i-1) - beg_(i-1)) then {
                beg_(i) := beg_(i-1), beg_(i-1) := beg_(i),
                end_(i) := end_(i-1), end_(i-1) := end_(i)
            } endif
        ] else
            i := i - 1
        endif
    ];

    { sorted := true, i := 0 };
    while (i < n - 1) { sorted := sorted and (a(i) <= a (i+1)), i := i + 1 }
]

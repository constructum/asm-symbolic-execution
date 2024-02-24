// https://bertdobbelaere.github.io/sorting_networks.html

function a : Integer -> Integer

function sorted : Boolean


rule Main = [
    
    seq
        if a(0) > a(2) then { a(0) := a(2), a(2) := a(0) } endif
        if a(0) > a(1) then { a(0) := a(1), a(1) := a(0) } endif
        if a(1) > a(2) then { a(1) := a(2), a(2) := a(1) } endif
    endseq;
 
    sorted := a(0) <= a(1) and a(1) <= a(2)

]

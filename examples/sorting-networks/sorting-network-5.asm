// https://bertdobbelaere.github.io/sorting_networks.html

function a : Integer -> Integer

function sorted : Boolean


rule Main = [
    
    seq
        par
            if a(0) > a(3) then { a(0) := a(3), a(3) := a(0) } endif
            if a(1) > a(4) then { a(1) := a(4), a(4) := a(1) } endif
        endpar
        par
            if a(0) > a(2) then { a(0) := a(2), a(2) := a(0) } endif
            if a(1) > a(3) then { a(1) := a(3), a(3) := a(1) } endif
        endpar
        par
            if a(0) > a(1) then { a(0) := a(1), a(1) := a(0) } endif
            if a(2) > a(4) then { a(2) := a(4), a(4) := a(2) } endif
        endpar
        par
            if a(1) > a(2) then { a(1) := a(2), a(2) := a(1) } endif
            if a(3) > a(4) then { a(3) := a(4), a(4) := a(3) } endif
        endpar
        if a(2) > a(3) then { a(2) := a(3), a(3) := a(2) } endif
    endseq;

    sorted := a(0) <= a(1) and a(1) <= a(2) and a(2) <= a(3) and a(3) <= a(4)

]

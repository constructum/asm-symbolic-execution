// https://bertdobbelaere.github.io/sorting_networks.html

function a : Integer -> Integer

function sorted : Boolean


rule Main = [
    
    seq
        par
            if a(0) > a(5) then { a(0) := a(5), a(5) := a(0) } endif
            if a(1) > a(3) then { a(1) := a(3), a(3) := a(1) } endif
            if a(2) > a(4) then { a(2) := a(4), a(4) := a(2) } endif
        endpar
        par
            if a(1) > a(2) then { a(1) := a(2), a(2) := a(1) } endif
            if a(3) > a(4) then { a(3) := a(4), a(4) := a(3) } endif
        endpar
        par
            if a(0) > a(3) then { a(0) := a(3), a(3) := a(0) } endif
            if a(2) > a(5) then { a(2) := a(5), a(5) := a(2) } endif
        endpar
        par
            if a(0) > a(1) then { a(0) := a(1), a(1) := a(0) } endif
            if a(2) > a(3) then { a(2) := a(3), a(3) := a(2) } endif
            if a(4) > a(5) then { a(4) := a(5), a(5) := a(4) } endif
        endpar
        par
            if a(1) > a(2) then { a(1) := a(2), a(2) := a(1) } endif
            if a(3) > a(4) then { a(3) := a(4), a(4) := a(3) } endif
        endpar    
    endseq;

    sorted := a(0) <= a(1) and a(1) <= a(2) and a(2) <= a(3) and a(3) <= a(4) and a(4) <= a(5)

]

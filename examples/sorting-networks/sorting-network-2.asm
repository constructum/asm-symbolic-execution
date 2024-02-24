// https://bertdobbelaere.github.io/sorting_networks.html

function a : Integer -> Integer

function sorted : Boolean


rule Main = [
    
    if a(0) > a(1) then { a(0) := a(1), a(1) := a(0) } endif;
 
    sorted := a(0) <= a(1)

]

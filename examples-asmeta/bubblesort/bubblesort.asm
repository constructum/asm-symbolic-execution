asm bubblesort

import ../STDL/StandardLibrary.asm


signature:
	static n : Integer
	controlled ii : Integer
	controlled j : Integer
	controlled a : Integer -> Integer
	controlled sorted : Boolean


definitions:
	function n = 5

	main rule r_Main = seq
		//--- sorting algorithm
    	ii := 0
    	while (ii < n) do seq
        	j := n - 1
        	while (j > ii) do seq
            	if a(j-1) > a(j)
            	then par a(j-1):=a(j) a(j):=a(j-1) endpar 
            	endif
            	j := j - 1
            endseq
        	ii := ii + 1
        endseq
		//--- verification that the array is sorted
	    par
	    	sorted := true
	    	ii := 0
	    endpar
	    while (ii < n - 1) do par
	    	sorted := sorted and (a(ii) <= a (ii+1))
	    	ii := ii + 1
	    endpar
	endseq


default init s0:
	function a($i in Integer) =
		switch $i
			case 0 : 5
			case 1 : 3
			case 2 : 2
			case 3 : 7
			case 4 : 4
		endswitch

asm matrixmult

import ../STDL/StandardLibrary.asm


signature:
	enum domain APa = { AB , BB | CC }
	static m : Integer
	static n : Integer
	static p : Integer
	controlled a : Prod(Integer, Integer) -> Integer
	controlled b : Prod(Integer, Integer) -> Integer
	controlled c : Prod(Integer, Integer) -> Integer
	controlled ii : Integer
	controlled j : Integer
	controlled k : Integer
	

definitions:
	function m = 2
	function n = 3
	function p = 4
	
	main rule r_Main =
		seq
	    	ii := 1
	    	while (ii <= m) do seq
		        j := 1
		        while (j <= p) do seq
		            par
		            	c(ii, j) := 0
		            	k := 1
		            endpar
		            while (k <= n) do par
		                c (ii, j) := c (ii, j) + a (ii, k) * b (k, j)
		                k := k + 1
		            endpar
		            j := j + 1
		        endseq
		        ii := ii + 1
	    	endseq
		endseq

		
default init s0:
	function a($i in Integer, $j in Integer) =
		switch ($i, $j)
			case (1, 1) : 1
			case (1, 2) : 2
			case (1, 3) : 3
			case (2, 1) : 4
			case (2, 2) : 5
			case (2, 3) : 6
		endswitch
	function b($i in Integer, $j in Integer) =
		switch ($i, $j)
			case (1, 1) : 1
			case (1, 2) : 2
			case (1, 3) : 3
			case (1, 4) : 4
			case (2, 1) : 5
			case (2, 2) : 6
			case (2, 3) : 7
			case (2, 4) : 8
			case (3, 1) : 9
			case (3, 2) : 10
			case (3, 3) : 11
			case (3, 4) : 12
		endswitch

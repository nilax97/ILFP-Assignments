fun power(base, index)=
	if index<1 then
		1
	else
		base * power(base, index - 1)

fun toInt(S)=
	if(String.size(S) = 0) then
		0
	else
		let
			val base = Char.ord( #"0" ); (* Base ASCII 0 value *)
			val x = String.size(S);
			val digit = Char.ord(String.sub(S,0));
			val value = digit - base;
			val exp = power(10, x-1);
			exception Invalid_Input_exception of string;
		in
			if (value<0 orelse value>9) then
				raise Invalid_Input_exception "Please enter a valid number"
			else
				value * exp + toInt(String.substring(S,1,x-1))
		end

fun fromString(S)=
	let
		val x = String.size(S);
		val y = x mod 4;
	in
		if x = 0 then
		[]
		else if y = 0 then
			toInt(String.substring(S,0,4))::fromString(String.substring(S,4, x-4))
		else
			toInt(String.substring(S,0,y))::fromString(String.substring(S,y, x - y))
	end

fun intstring x =
	if(x>1000) then
		Int.toString(x)
	else if (x>100) then
		"0" ^ Int.toString(x)
	else if (x>10) then
		"00" ^ Int.toString(x)
	else
		"000" ^ Int.toString(x)

fun toString_helper([])= "" |
	toString_helper(h::t)=
		intstring(h) ^ toString_helper(t)

fun toString([]) = "" |
	toString(h::t)=
	Int.toString(h) ^ toString_helper(t)

fun length [] = 0 | (* Length of a list *)
	length(h::t)= 1 + length(t)

fun pad(x, 0) = x | (* Add extra 0's at the end of a list *)
	pad([],n) = (0 :: pad([], n-1)) |
	pad(h::t, n) = (0 :: pad(h::t,n-1))

fun shift(x,0) = [] | (* Add extra 0's at the start of a list *)
	shift(h::t,m) = h::shift(t,m) |
	shift([],m) = 0::shift([],m-1)

fun split(x,0) = ([],x) | (* Split a list into two components, one with m slices *)
	split([],m) = ([],[]) |
	split(h::t, m)=
		let
			val (x,y) = split(t, m-1);
		in
			(h::x,y)
		end

fun clean [] = [] | (* Remove trailing 0s from a list *)
	clean(h::t)=
	if (h = 0 andalso length(t) > 0) then
		clean(t)
	else (h::t)

fun add_helper((hx::tx),(hy::ty))= (* Helper function to add two lists *)
		let
			val (carry,sum) = add_helper(tx,ty)
			val res = (hx + hy + carry) mod 10000
			val f_car = (hx + hy + carry) div 10000
		in
			(f_car, (res::sum))
		end
	|
	add_helper(x,y) = (0, [])

fun add(x,y)= (* Add the lists in a O(n) time *)
	let
		val lenX = length(x);
		val lenY = length(y);
	in
		if(lenX > lenY) then
			let
				val (carry,sum) = add_helper(x, pad(y, lenX - lenY))
			in
				if(carry>0) then
					carry::sum
				else
					sum
			end
			
		else
			let
				val (carry,sum) = add_helper(y, pad(x, lenY - lenX))
			in
				if(carry>0) then
					carry::sum
				else
					sum
			end
	end 

fun karatsuba [x] [y]= (* Function to implement Karatsuba Algorithm for 1e4 Base lists *)
	let
		val mult = x * y
	in
		if(mult >= 10000) then
			(mult div 10000) :: [mult mod 10000]
		else
			[mult]
	end
	|
	karatsuba (hx::tx) (hy::ty)=
	let
		val n_x = length(tx) + 1;
		val n_y = length(ty) + 1;
		val m = (n_x + 1) div 2;
		val (x1,x0) = split((hx::tx), n_x-m);
		val (y1,y0) = split((hy::ty), n_y-m);
		val z2 = shift(karatsuba x1 y1,2*m);
		val z0 = karatsuba x0 y0;
		val z1 = shift(add(karatsuba x1 y0, karatsuba x0 y1),m);
	in
		clean(add( z2, add(z1, z0)))
	end
	|
	karatsuba x y=[]

fun subtract([],1) = [] (* Function to subtract an int from a list of ints *)
	|
	subtract(x,t)=
	if(length(x)>1) then
		(hd x :: subtract(tl x, t))
	else
		let
			val x1 = hd(x) - t;
		in
			(x1 :: tl x)
		end

fun fact_tail([], p) = p | (* Tail Recersion function for factorial *)
	fact_tail([0],p) = p |
	fact_tail(n,p)=
	let
		val iter = clean(subtract(n,1))
		val prod = clean(karatsuba n p)
	in
		fact_tail(iter,prod)
	end

fun factorial_helper([])=[1] |
	factorial_helper([0])= [1] |
	factorial_helper(x)=
		fact_tail(x,[1])

fun factorial x=
	toString(clean(factorial_helper(fromString(x))))
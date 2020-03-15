use "signatureLAMBDAFLX.sml";

structure LambdaFlx : LAMBDAFLX = 
struct
	datatype lterm = term 							(* term from FLX *)
					| VAR of string					(* variables *)
					| Z								(* zero *)
					| T								(* true *)
					| F								(* false *)
					| P of lterm					(* Predecessor *)
					| S of lterm					(* Successor *)
					| ITE of lterm * lterm * lterm	(* If then else *)
					| IZ of lterm					(* is zero *)
					| GTZ of lterm					(* is greater than zero *)
					| LAMBDA of lterm * lterm		(* lambda x [lterm] *)
					| APP of lterm * lterm			(* application of lambda terms, i.e. (L M) *)

	exception Not_wellformed
	exception Not_nf
	exception Not_int
	exception Not_welltyped

	fun clean [] = []
				(*| clean (#" "::t) = clean(t)*)
				| clean(h::t) = h::clean(t)
	fun join_vars [] = []
				| join_vars((#"I")::(#"T")::(#"E")::tl) = "ITE"::join_vars(tl)
				| join_vars((#"I")::(#"Z")::tl) = "IZ"::join_vars(tl)
				| join_vars((#"G")::(#"T")::(#"Z")::tl) = "GTZ"::join_vars(tl)
				| join_vars((#"L")::(#"A")::(#"M")::(#"B")::(#"D")::(#"A")::tl) = "LAMBDA"::join_vars(tl)
				| join_vars (h::t) = 
					let
						val clean_t = join_vars(t)
					in
						if(Char.isUpper(h) orelse h = #"," orelse h = #"(" orelse h = #")" orelse h = #"<" orelse h = #">" orelse h = #"[" orelse h = #"]") then
							""::Char.toString(h)::clean_t
						else if(h = #" ") then
							""::clean_t
						else
							if(t=[]) then
								[Char.toString(h)]
							else
								Char.toString(h) ^ List.hd(clean_t) :: List.tl(clean_t)
					end
	fun make_vars [] = []
				| make_vars(""::t) = make_vars(t)
				| make_vars(h::t) = VAR(h) :: make_vars(t)
	fun check_var(VAR(s))=1
		| check_var(_)=0
	fun reduce_terms [] = []
				| reduce_terms(VAR("Z")::tl) = Z::reduce_terms(tl)
				| reduce_terms (VAR("T")::tl) = T::reduce_terms(tl)
				| reduce_terms (VAR("F")::tl) = F::reduce_terms(tl)
				| reduce_terms (VAR(" ")::tl) = reduce_terms(tl)
				| reduce_terms (VAR("(")::VAR("P")::(x)::VAR(")")::tl) = P(List.hd(reduce_terms[x]))::reduce_terms(tl)
				| reduce_terms (VAR("(")::VAR("S")::(x)::VAR(")")::tl) = S(List.hd(reduce_terms[x]))::reduce_terms(tl)
				| reduce_terms (VAR("(")::VAR("IZ")::(x)::VAR(")")::tl) = IZ(List.hd(reduce_terms[x]))::reduce_terms(tl)
				| reduce_terms (VAR("(")::VAR("GTZ")::(x)::VAR(")")::tl) = GTZ(List.hd(reduce_terms[x]))::reduce_terms(tl)
				| reduce_terms (VAR("(")::VAR("ITE")::VAR("<")::(a)::VAR(",")::(b)::VAR(",")::(c)::VAR(">")::VAR(")")::tl) = ITE((List.hd(reduce_terms[a])),(List.hd(reduce_terms[b])),(List.hd(reduce_terms[c])))::reduce_terms(tl)
				| reduce_terms (VAR("LAMBDA")::(a)::VAR("[")::(b)::VAR("]")::tl) = 
					let
						val a1 = List.hd(reduce_terms[a])
						val b1 = List.hd(reduce_terms[b])
					in
						if(check_var(a1)=1)then
							LAMBDA(a1,b1)::reduce_terms(tl)
						else
							raise Not_wellformed
					end
				| reduce_terms (VAR("(")::(a)::(b)::VAR(")")::tl) = APP(List.hd(reduce_terms[a]),List.hd(reduce_terms[b]))::reduce_terms(tl)
				| reduce_terms(h::tl) = h::reduce_terms(tl)
	fun compare([],[]) = true
				| compare(L,[]) = false
				| compare([],L) = false
				| compare(L1 as (h1::t1), L2 as (h2::t2)) =
					if(h1=h2) then
						compare(t1,t2)
					else
						false
	fun make_terms [] = []
				| make_terms [h] = [h]
				| make_terms(L as h::t) =
				let
					val L1 = reduce_terms(h::t)
				in
					if(compare(L1,L)) then
						L1
					else
						make_terms(L1)
				end
	fun substitute(x,Z,n) = Z
				| substitute(x,T,n) = T
				| substitute(x,F,n) = F
				| substitute(x,P(lterm),n) = 
					let
						val sub = substitute(x,lterm,n)
					in
						P(sub)
					end
				| substitute(x,S(lterm),n) = 
					let
						val sub = substitute(x,lterm,n)
					in
						S(sub)
					end
				| substitute(x,IZ(lterm),n) = 
					let
						val sub = substitute(x,lterm,n)
					in
						IZ(sub)
					end
				| substitute(x,GTZ(lterm),n) = 
					let
						val sub = substitute(x,lterm,n)
					in
						GTZ(sub)
					end
				| substitute(x,ITE(lterm1,lterm2,lterm3),n) = 
					let
						val sub1 = substitute(x,lterm1,n)
						val sub2 = substitute(x,lterm2,n)
						val sub3 = substitute(x,lterm3,n)
					in
						ITE(sub1,sub2,sub3)
					end
				| substitute(x,APP(lterm1,lterm2),n) = 
					let
						val sub1 = substitute(x,lterm1,n)
						val sub2 = substitute(x,lterm2,n)
					in
						APP(sub1,sub2)
					end
				| substitute(x,LAMBDA(lterm1,lterm2),n) =
					let
						val sub2 = substitute(x,lterm2,n)
					in
						if(x=lterm1) then
							raise Not_wellformed
						else
							LAMBDA(lterm1,sub2)
					end
				| substitute(x,VAR(t),n) = 
					if(x=VAR(t)) then
						VAR(t ^ Int.toString(n))
					else
						VAR(t)
	fun alpha_sub(Z,n) = (Z,n)
				| alpha_sub(T,n) = (T,n)
				| alpha_sub(F,n) = (F,n)
				| alpha_sub(P(lterm),n) =
					let
						val (subbed,n1) = alpha_sub(lterm,n)
					in
						(P(subbed),n1)
					end
				| alpha_sub(S(lterm),n) =
					let
						val (subbed,n1) = alpha_sub(lterm,n)
					in
						(S(subbed),n1)
					end
				| alpha_sub(IZ(lterm),n) =
					let
						val (subbed,n1) = alpha_sub(lterm,n)
					in
						(IZ(subbed),n1)
					end
				| alpha_sub(GTZ(lterm),n) =
					let
						val (subbed,n1) = alpha_sub(lterm,n)
					in
						(GTZ(subbed),n1)
					end
				| alpha_sub(ITE(lterm1,lterm2,lterm3),n) =
					let
						val (subbed1,n1) = alpha_sub(lterm1,n)
						val (subbed2,n2) = alpha_sub(lterm2,n1)
						val (subbed3,n3) = alpha_sub(lterm3,n2)
					in
						(ITE(subbed1,subbed2,subbed3),n3)
					end
				| alpha_sub(APP(lterm1,lterm2),n) =
					let
						val (subbed1,n1) = alpha_sub(lterm1,n)
						val (subbed2,n2) = alpha_sub(lterm2,n1)
					in
						(APP(subbed1,subbed2),n2)
					end
				| alpha_sub(LAMBDA(lterm1, lterm2),n) =
					let
						val lterm3 = substitute(lterm1,lterm1,n)
						val lterm4 = substitute(lterm1,lterm2,n)
						val (subbed2,n2) = alpha_sub(lterm4,n+1)
						
					in
						(LAMBDA(lterm3,subbed2),n2+1)
					end
				| alpha_sub(VAR(x),n) = (VAR(x),n)
	fun fromString(Str) =
				let
					val S_clean = clean(String.explode(Str))
					val S_join = join_vars(S_clean)
					val S_made = make_vars(S_join)
					val S_term = make_terms(S_made)
				in
					if(List.length(S_term) > 1) then
						raise Not_wellformed
					else
						let
							val ans = List.hd(S_term)
							val (final,no) = alpha_sub(ans,0)
						in
							final
						end
				end

	fun toString (VAR(t)) = t
		| toString (Z) = "Z"
		| toString (T) = "T"
		| toString (F) = "F"
		| toString (P(lterm)) = "(P " ^ toString(lterm) ^ ")"
		| toString (S(lterm)) = "(S " ^ toString(lterm) ^ ")"
		| toString (IZ(lterm)) = "(IZ " ^ toString(lterm) ^ ")"
		| toString (GTZ(lterm)) = "(GTZ " ^ toString(lterm) ^ ")"
		| toString (ITE(term1, term2, term3)) = "(ITE <" ^ toString(term1) ^ "," ^ toString(term2) ^ "," ^ toString(term3) ^ ">)"
		| toString (LAMBDA(term1,term2)) = "LAMBDA " ^ toString(term1) ^ "[" ^ toString(term2) ^ "]"
		| toString (APP(term1,term2)) = "(" ^ toString(term1) ^ " " ^ toString(term2) ^ ")"

	fun fromInt(N) =
		if(N = 0) then
			Z
		else if(N > 0) then
			S(fromInt(N-1))
		else
			P(fromInt(N+1))

	fun toIntp(n) = 
		case n of
			Z => 0
		| S(n) => 1 + toIntp(n)
		| P(n) => raise Not_nf
		| _ => raise Not_int
	fun toIntn(n) = 
		case n of
			Z => 0
		| P(n) => ~1 + toIntn(n)
		| S(n) => raise Not_nf
		| _ => raise Not_int
	fun toInt(n) = 
		case n of
			Z => 0
		| S(n) => 1 + toIntp(n)
		| P(n) => ~1 + toIntn(n)
		| _ => raise Not_int

	datatype ltype = BOOL
	| INT
	| VARIABLE of lterm
	| FUNCTION of ltype * ltype
	| PRODUCT of ltype * ltype
	fun check_list(x,[],M,type_val) = (x,type_val)::M
		| check_list(x,L as (h,h_t)::t,M,type_val)=
			if(x = h) then
				if(h_t = type_val) then
					L @ M
				else
					raise Not_welltyped
			else
				check_list(x,t,(h,h_t)::M,type_val)
	fun find_list(x:string,[])=
		VARIABLE (VAR(x))
		| find_list(x:string,(h,h_t)::t)=
			if(x=h) then
				h_t
			else
				find_list(x,t)
	fun update_list(x,y,[])=
		[]
		| update_list(x,y,(h,h_t)::t)=
			if(x=h_t) then
				let
					val t_update = update_list(x,y,t)
				in
					(h,y)::t_update
				end
			else
				let
					val t_update = update_list(x,y,t)
				in
					(h,h_t)::t_update
				end
	fun is_var(VARIABLE(x)) = 1
		| is_var(_) = 0
	fun check_ite(INT,INT,L) = (INT,L)
		| check_ite(BOOL,BOOL,L) = (BOOL,L)
		| check_ite(BOOL, VARIABLE(x),L) = 
			let
				val L1 = update_list(VARIABLE(x),BOOL,L)
			in
				(BOOL,L1)
			end
		| check_ite(VARIABLE(x),BOOL,L) = 
			let
				val L1 = update_list(VARIABLE(x),BOOL,L)
			in
				(BOOL,L1)
			end
		| check_ite(INT, VARIABLE(x),L) = 
			let
				val L1 = update_list(VARIABLE(x),INT,L)
			in
				(INT,L1)
			end
		| check_ite(VARIABLE(x),INT,L) = 
			let
				val L1 = update_list(VARIABLE(x),INT,L)
			in
				(INT,L1)
			end
		| check_ite(VARIABLE(x),VARIABLE(y),L) = 
			let
				val L1 = update_list(VARIABLE(x),VARIABLE(y),L)
			in
				(VARIABLE(y),L1)
			end
		| check_ite(_,_,_) = raise Not_welltyped;
	fun check_app(VARIABLE(x),ltype1,L) =
		let
			val L1 = update_list(VARIABLE(x), FUNCTION(ltype1, VARIABLE(x)),L)
		in
			(VARIABLE(x),L1)
		end
		| check_app(FUNCTION(ltype1,ltype2),ltype3,L) =
			if(ltype1 = ltype3) then
				(ltype2,L)
			else
				let
					val check_1 = is_var(ltype1)
					val check_3 = is_var(ltype3)
				in
					if(check_1=1 andalso check_3=1) then
						let
							val L1 = update_list(ltype3,ltype1,L)
						in
							(ltype2,L1)
						end
					else if(check_1 = 1) then
						let
							val L1 = update_list(ltype1,ltype3,L)
						in
							(ltype2,L1)
						end
					else if(check_3 = 1) then
						let
							val L1 = update_list(ltype3,ltype1,L)
						in
							(ltype2,L1)
						end
					else
						raise Not_welltyped
				end
		| check_app(_,_,_) = raise Not_int
	fun get_type (Z,L) = (INT,L)
		| get_type (T,L) = (BOOL,L)
		| get_type (F,L) = (BOOL,L)
		| get_type (P(VAR(x)),L) =
			let
				val L1 = check_list(x,L,[],INT)
			in
				(INT,L1)
			end
		| get_type (P(lterm),L) = 
			let
				val (termtype,L1) = get_type(lterm,L)
			in
				if(termtype = INT) then
					(INT,L1)
				else
					raise Not_welltyped
			end
		| get_type (S(VAR(x)),L) =
			let
				val L1 = check_list(x,L,[],INT)
			in
				(INT,L1)
			end
		| get_type (S(lterm),L) = 
			let
				val (termtype,L1) = get_type(lterm,L)
			in
				if(termtype = INT) then
					(INT,L1)
				else
					raise Not_welltyped
			end
		| get_type (IZ(VAR(x)),L) =
			let
				val L1 = check_list(x,L,[],INT)
			in
				(BOOL,L1)
			end
		| get_type (IZ(lterm),L) = 
			let
				val (termtype,L1) = get_type(lterm,L)
			in
				if(termtype = INT) then
					(BOOL,L1)
				else
					raise Not_welltyped
			end
		| get_type (GTZ(VAR(x)),L) =
			let
				val L1 = check_list(x,L,[],INT)
			in
				(BOOL,L1)
			end
		| get_type (GTZ(lterm),L) = 
			let
				val (termtype,L1) = get_type(lterm,L)
			in
				if(termtype = INT) then
					(BOOL,L1)
				else
					raise Not_welltyped
			end
		| get_type(ITE(VAR(x),VAR(y),VAR(z)),L) =
			let
				val L1 = check_list(x,L,[],BOOL)
				val y_type = find_list(y,L1)
				val z_type = find_list(z,(y,y_type)::L1)
				val check_y = is_var(y_type)
				val check_z = is_var(z_type)
			in
				if(check_y=1 andalso check_z=1) then
					check_ite(y_type,z_type,(y,y_type)::(z,z_type)::L1)
				else if(check_y=1) then
					check_ite(y_type,z_type,(y,y_type)::L1)
				else if (check_z=1) then
					check_ite(y_type,z_type,(z,z_type)::L1)
				else
					check_ite(y_type,z_type,L1)
			end
		| get_type(ITE(lterm1,VAR(y),VAR(z)),L) =
			let
				val (x_type,L1) = get_type(lterm1,L)
				val y_type = find_list(y,L1)
				val z_type = find_list(z,(y,y_type)::L1)
				val check_y = is_var(y_type)
				val check_z = is_var(z_type)
			in
				if(x_type= BOOL) then
					if(check_y=1 andalso check_z=1) then
						check_ite(y_type,z_type,(y,y_type)::(z,z_type)::L1)
					else if(check_y=1) then
						check_ite(y_type,z_type,(y,y_type)::L1)
					else if (check_z=1) then
						check_ite(y_type,z_type,(z,z_type)::L1)
					else
						check_ite(y_type,z_type,L1)
				else
					raise Not_welltyped
			end
		| get_type(ITE(VAR(x),lterm2,VAR(z)),L) =
			let
				val L1 = check_list(x,L,[],BOOL)
				val (y_type,L2) = get_type(lterm2,L1)
				val z_type = find_list(z,L2)
				val check_z = is_var(z_type)
			in
				if(check_z=1) then
					check_ite(y_type,z_type,(z,z_type)::L2)
				else
					check_ite(y_type,z_type,L2)
			end
		| get_type(ITE(lterm1,lterm2,VAR(z)),L) =
			let
				val (x_type,L1) = get_type(lterm1,L)
				val (y_type,L2) = get_type(lterm2,L1)
				val z_type = find_list(z,L2)
				val check_z = is_var(z_type)
			in
				if(x_type= BOOL) then
					if(check_z=1) then
						check_ite(y_type,z_type,(z,z_type)::L2)
					else
						check_ite(y_type,z_type,L2)
				else
					raise Not_welltyped
			end
		| get_type(ITE(VAR(x),VAR(z),lterm2),L) =
			let
				val L1 = check_list(x,L,[],BOOL)
				val (y_type,L2) = get_type(lterm2,L1)
				val z_type = find_list(z,L2)
				val check_z = is_var(z_type)
			in
				if(check_z=1) then
					check_ite(y_type,z_type,(z,z_type)::L2)
				else
					check_ite(y_type,z_type,L2)
			end
		| get_type(ITE(lterm1,VAR(z),lterm2),L) =
			let
				val (x_type,L1) = get_type(lterm1,L)
				val (y_type,L2) = get_type(lterm2,L1)
				val z_type = find_list(z,L2)
				val check_z = is_var(z_type)
			in
				if(x_type= BOOL) then
					if(check_z=1) then
						check_ite(y_type,z_type,(z,z_type)::L2)
					else
						check_ite(y_type,z_type,L2)
				else
					raise Not_welltyped
			end
		| get_type(ITE(VAR(x),lterm2,lterm3),L) =
			let
				val L1 = check_list(x,L,[],BOOL)
				val (y_type,L2) = get_type(lterm2,L1)
				val (z_type,L3) = get_type(lterm3,L2)
			in
				check_ite(y_type,z_type,L3)
			end
		| get_type(ITE(lterm1,lterm2,lterm3),L) =
			let
				val (x_type,L1) = get_type(lterm1,L)
				val (y_type,L2) = get_type(lterm2,L1)
				val (z_type,L3) = get_type(lterm3,L2)
			in
				if(x_type= BOOL) then
					check_ite(y_type,z_type,L3)
				else
					raise Not_welltyped
			end
		| get_type(LAMBDA(VAR(y),VAR(z)),L)=
			let
				val y_type = find_list(y,L)
				val z_type = find_list(z,(y,y_type)::L)
				val check_y = is_var(y_type)
				val check_z = is_var(z_type)
			in
				if(check_y=1 andalso check_z=1) then
					(FUNCTION(y_type,z_type),(y,y_type)::(z,z_type)::L)
				else if(check_y=1) then
					(FUNCTION(y_type,z_type),(y,y_type)::L)
				else if (check_z=1) then
					(FUNCTION(y_type,z_type),(z,z_type)::L)
				else
					(FUNCTION(y_type,z_type),L)
			end
		| get_type(LAMBDA(VAR(x),lterm),L)=
			let
				val (y_type,L1) = get_type(lterm,L)
				val x_type = find_list(x,L1)
				val check_x = is_var(x_type)
			in
				if(check_x=1) then
					(FUNCTION(x_type,y_type),(x,x_type)::L1)
				else
					(FUNCTION(x_type,y_type),L1)
			end
		| get_type(APP(VAR(y),VAR(z)),L) =
			let
				val y_type = find_list(y,L)
				val z_type = find_list(z,(y,y_type)::L)
				val check_y = is_var(y_type)
				val check_z = is_var(z_type)
			in
				if(y=z) then
					raise Not_welltyped
				else
					if(check_y=1 andalso check_z=1) then
						check_app(y_type,z_type,(y,y_type)::(z,z_type)::L)
					else if(check_y=1) then
						check_app(y_type,z_type,(y,y_type)::L)
					else if (check_z=1) then
						check_app(y_type,z_type,(z,z_type)::L)
					else
						check_app(y_type,z_type,L)
			end
		| get_type(APP(VAR(y),lterm),L) =
			let
				val (z_type,L1) = get_type(lterm,L)
				val y_type = find_list(y,L)
				val check_y = is_var(y_type)
			in
				if(check_y = 1) then
					check_app(y_type,z_type,(y,y_type)::L1)
				else
					check_app(y_type,z_type,L1)
			end
		| get_type(APP(lterm,VAR(y)),L) = 
			let
				val (z_type,L1) = get_type(lterm,L)
				val y_type = find_list(y,L)
				val check_y = is_var(y_type)
			in
				if(check_y = 1) then
					check_app(z_type,y_type,(y,y_type)::L1)
				else
					check_app(z_type,y_type,L1)
			end
		| get_type(APP(lterm1,lterm2),L) = 
			let
				val (y_type,L1) = get_type(lterm1,L)
				val (z_type,L2) = get_type(lterm2,L1)
			in
				check_app(y_type,z_type,L2)
			end
		| get_type(VAR(x),L) = (VARIABLE(VAR(x)),L)
		| get_type(_,_)=
			raise Not_wellformed

	fun substitute_nf(x,Z,L) = Z
		| substitute_nf(x,T,L) = T
		| substitute_nf(x,F,L) = F
		| substitute_nf(x,P(lterm),L) = 
			let
				val sub = substitute_nf(x,lterm,L)
			in
				P(sub)
			end
		| substitute_nf(x,S(lterm),L) = 
			let
				val sub = substitute_nf(x,lterm,L)
			in
				S(sub)
			end
		| substitute_nf(x,IZ(lterm),L) = 
			let
				val sub = substitute_nf(x,lterm,L)
			in
				IZ(sub)
			end
		| substitute_nf(x,GTZ(lterm),L) = 
			let
				val sub = substitute_nf(x,lterm,L)
			in
				GTZ(sub)
			end
		| substitute_nf(x,ITE(lterm1,lterm2,lterm3),L) = 
			let
				val sub1 = substitute_nf(x,lterm1,L)
				val sub2 = substitute_nf(x,lterm2,L)
				val sub3 = substitute_nf(x,lterm3,L)
			in
				ITE(sub1,sub2,sub3)
			end
		| substitute_nf(x,APP(lterm1,lterm2),L) = 
			let
				val sub1 = substitute_nf(x,lterm1,L)
				val sub2 = substitute_nf(x,lterm2,L)
			in
				APP(sub1,sub2)
			end
		| substitute_nf(x,LAMBDA(lterm1,lterm2),L) =
			let
				val sub2 = substitute_nf(x,lterm2,L)
			in
				if(x=lterm1) then
					raise Not_wellformed
				else
					LAMBDA(lterm1,sub2)
			end
		| substitute_nf(x,VAR(t),L) = 
			if(x=VAR(t)) then
				L
			else
				VAR(t)
	fun betanf_helper (P(S(lterm))) = betanf_helper(lterm)
		| betanf_helper (S(P(lterm))) = betanf_helper(lterm)
		| betanf_helper (IZ(ITE(cond,term1,term2))) =
			let
				val cond_n = betanf_helper(IZ(cond))
				val term1_n = betanf_helper(IZ(term1))
				val term2_n = betanf_helper(IZ(term2))
			in
				betanf_helper(ITE(cond_n,term1_n,term2_n))
			end
		| betanf_helper (GTZ(ITE(cond,term1,term2))) =
			let
				val cond_n = betanf_helper(GTZ(cond))
				val term1_n = betanf_helper(GTZ(term1))
				val term2_n = betanf_helper(GTZ(term2))
			in
				betanf_helper(ITE(cond_n,term1_n,term2_n))
			end
		| betanf_helper (P(ITE(cond,term1,term2))) =
			let
				val cond_n = betanf_helper(P(cond))
				val term1_n = betanf_helper(P(term1))
				val term2_n = betanf_helper(P(term2))
			in
				betanf_helper(ITE(cond_n,term1_n,term2_n))
			end
		| betanf_helper (S(ITE(cond,term1,term2))) =
			let
				val cond_n = betanf_helper(S(cond))
				val term1_n = betanf_helper(S(term1))
				val term2_n = betanf_helper(S(term2))
			in
				betanf_helper(ITE(cond_n,term1_n,term2_n))
			end
		| betanf_helper (ITE(cond,term1,term2)) = 
			let
				fun betanf_helper_ITE (ITE(T,lterm,_)) = lterm
					| betanf_helper_ITE (ITE(F,_,lterm)) = lterm
					| betanf_helper_ITE (ITE(cond,term1,term2)) = 
						if(term1 = term2) then
							let
								val (type_val,L) = get_type(ITE(cond,term1,term2),[])
							in
								term1
							end
						else
							ITE(cond,term1,term2)
				 | betanf_helper_ITE (lterm) = lterm
				val cond_n = betanf_helper(cond)
				val term1_n = betanf_helper(term1)
				val term2_n = betanf_helper(term2)
			in
				betanf_helper_ITE(ITE(cond_n,term1_n,term2_n))
			end
		| betanf_helper (IZ(Z)) = T
		| betanf_helper (GTZ(Z)) = F
		| betanf_helper (IZ(lterm)) = 
			let
				fun betanf_helper_IZ(P(lterm)) = 
						if(betanf_helper_IZ(lterm)=T orelse betanf_helper_IZ(lterm)=F) then
							F
						else
							IZ(P(lterm))
					| betanf_helper_IZ(S(lterm)) = 
						if(betanf_helper_IZ(lterm)=T orelse betanf_helper_IZ(lterm)=F) then
							F
						else
							IZ(S(lterm))
					| betanf_helper_IZ(Z) = T
					| betanf_helper_IZ(value) = IZ(value)
				val term_n = betanf_helper(lterm)
			in
				betanf_helper_IZ(term_n)
			end
		| betanf_helper (GTZ(lterm)) =
			let
				fun betanf_helper_GTZ(S(lterm)) = 
						if(lterm = Z orelse betanf_helper_GTZ(lterm) = T) then
							T
						else
							GTZ(S(lterm))
					| betanf_helper_GTZ(P(lterm)) = 
						if(lterm = Z orelse betanf_helper_GTZ(lterm) = F) then
							F
						else
							GTZ(P(lterm))
					| betanf_helper_GTZ(Z) = F
					| betanf_helper_GTZ(value) = GTZ(value)
				val term_n = betanf_helper(lterm)
			in
				betanf_helper_GTZ(term_n)
			end
		| betanf_helper(Z) = Z
		| betanf_helper(T) = T
		| betanf_helper(F) = F
		| betanf_helper(S(lterm)) = 
			let
				fun betanf_helper_S(P(lterm)) = lterm
				| betanf_helper_S(lterm) = S(lterm)
				val term_n = betanf_helper(lterm)
			in
				betanf_helper_S(term_n)
			end
		| betanf_helper(P(lterm)) = 
			let
				fun betanf_helper_P(S(lterm)) = lterm
				| betanf_helper_P(lterm) = P(lterm)
				val term_n = betanf_helper(lterm)
			in
				betanf_helper_P(term_n)
			end
		| betanf_helper(VAR(x)) = VAR(x)
		| betanf_helper(APP(LAMBDA(term1,term2),term3))=
			let
				val term1_nf = betanf_helper(term1)
				val term2_nf = betanf_helper(term2)
				val term3_nf = betanf_helper(term3)
			in
				if(check_var(term1_nf)=1) then
					let
						val result = substitute_nf(term1_nf, term2_nf, term3_nf)
					in
						betanf_helper(result)
					end
					
				else
					raise Not_wellformed
			end
		| betanf_helper(APP(term1,term2))=
			let
				val term1_nf = betanf_helper(term1)
				val term2_nf = betanf_helper(term2)
			in
				if(term1_nf = term2_nf) then
					raise Not_welltyped
				else
					APP(term1_nf,term2_nf)
			end
		| betanf_helper(LAMBDA(term1,term2))=
			let
				val term1_nf = betanf_helper(term1)
				val term2_nf = betanf_helper(term2)
			in
				if(check_var(term1_nf)=1) then
					LAMBDA(term1_nf,term2_nf)
				else
					raise Not_wellformed
			end
	fun betanf_r(lterm1)=
		let
			val res = betanf_helper(lterm1)
		in
			if(res = lterm1) then
				res
			else
				betanf_r(res)
		end

	fun isWellTyped(lterm) = 
		let
			val lterm1 = fromString(toString(lterm))
			val result1 = (case (get_type(lterm1,[])) of 
							(type_val,list_term) => (1))
						handle Not_int => (~1)
							| Not_welltyped => (0)
							| Not_wellformed => (raise	Not_wellformed);
		in
			if(result1 = ~1)then
				false
			else if(result1 = 1)then
				true
			else
				let
					val lterm2 = betanf_r(lterm1)
					val result2 = (case (get_type(lterm2,[])) of 
							(type_val,list_term) => (true))
						handle Not_welltyped => (false)
							| Not_wellformed => (raise	Not_wellformed);
				in
					result2
				end
		end

	fun betanf(lterm)=
		let
			val type_check = isWellTyped(lterm)
		in
			if(type_check=false) then
				raise Not_welltyped
			else
				betanf_r(lterm)
		end
end (* struct *)
use "signatureFLX.sml";

structure Flx : FLX = 
struct
	datatype term = VAR of string (* variable *)
                  | Z           (* zero *)
                  | T           (* true *)
                  | F           (* false *)
                  | P of term   (* Predecessor *)
                  | S of term   (* Successor *)
                  | ITE of term * term * term   (* If then else *)
                  | IZ of term  (* is zero *)
                  | GTZ of term (* is greater than zero *)
    
    exception Not_wellformed
    exception Not_nf
    exception Not_int

    local
      fun clean [] = []
        (*| clean (#" "::t) = clean(t)*)
        | clean(h::t) = h::clean(t)
      fun join_vars [] = []
        | join_vars((#"I")::(#"T")::(#"E")::tl) = "ITE"::join_vars(tl)
        | join_vars((#"I")::(#"Z")::tl) = "IZ"::join_vars(tl)
        | join_vars((#"G")::(#"T")::(#"Z")::tl) = "GTZ"::join_vars(tl)
        | join_vars (h::t) = 
          let
            val clean_t = join_vars(t)
          in
            if(Char.isUpper(h) orelse h = #"," orelse h = #"(" orelse h = #")" orelse h = #"<" orelse h = #">") then
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
      fun reduce_terms [] = []
        | reduce_terms(VAR("Z")::tl) = Z::reduce_terms(tl)
        | reduce_terms (VAR("T")::tl) = T::reduce_terms(tl)
        | reduce_terms (VAR("F")::tl) = F::reduce_terms(tl)
        | reduce_terms (VAR(" ")::tl) = reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("P")::(x:term)::VAR(")")::tl) = P(List.hd(reduce_terms[x]))::reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("S")::(x:term)::VAR(")")::tl) = S(List.hd(reduce_terms[x]))::reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("IZ")::(x:term)::VAR(")")::tl) = IZ(List.hd(reduce_terms[x]))::reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("GTZ")::(x:term)::VAR(")")::tl) = GTZ(List.hd(reduce_terms[x]))::reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("ITE")::VAR("<")::(a:term)::VAR(",")::(b:term)::VAR(",")::(c:term)::VAR(">")::VAR(")")::tl) = ITE((List.hd(reduce_terms[a])),(List.hd(reduce_terms[b])),(List.hd(reduce_terms[c])))::reduce_terms(tl)
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
            raise Not_wellformed
          else
            make_terms(L1)
        end
    in
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
            List.hd(S_term)
        end
    end

    fun toString (VAR(t)) = t
      | toString (Z) = "Z"
      | toString (T) = "T"
      | toString (F) = "F"
      | toString (P(term)) = "(P " ^ toString(term) ^ ")"
      | toString (S(term)) = "(S " ^ toString(term) ^ ")"
      | toString (IZ(term)) = "(IZ " ^ toString(term) ^ ")"
      | toString (GTZ(term)) = "(GTZ " ^ toString(term) ^ ")"
      | toString (ITE(term1, term2, term3)) = "(ITE <" ^ toString(term1) ^ "," ^ toString(term2) ^ "," ^ toString(term3) ^ ">)"

    fun fromInt(N) =
      if(N = 0) then
        Z
      else if(N > 0) then
        S(fromInt(N-1))
      else
        P(fromInt(N+1))

    local
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
    in
      fun toInt(n) = 
        case n of
          Z => 0
        | S(n) => 1 + toIntp(n)
        | P(n) => ~1 + toIntn(n)
        | _ => raise Not_int
    end
        
    fun normalize (P(S(term))) = normalize(term)
      | normalize (S(P(term))) = normalize(term)
      | normalize (IZ(ITE(cond,term1,term2))) =
        let
          val cond_n = normalize(IZ(cond))
          val term1_n = normalize(IZ(term1))
          val term2_n = normalize(IZ(term2))
        in
          normalize(ITE(cond_n,term1_n,term2_n))
        end
      | normalize (GTZ(ITE(cond,term1,term2))) =
        let
          val cond_n = normalize(GTZ(cond))
          val term1_n = normalize(GTZ(term1))
          val term2_n = normalize(GTZ(term2))
        in
          normalize(ITE(cond_n,term1_n,term2_n))
        end
      | normalize (P(ITE(cond,term1,term2))) =
        let
          val cond_n = normalize(P(cond))
          val term1_n = normalize(P(term1))
          val term2_n = normalize(P(term2))
        in
          normalize(ITE(cond_n,term1_n,term2_n))
        end
      | normalize (S(ITE(cond,term1,term2))) =
        let
          val cond_n = normalize(S(cond))
          val term1_n = normalize(S(term1))
          val term2_n = normalize(S(term2))
        in
          normalize(ITE(cond_n,term1_n,term2_n))
        end
      | normalize (ITE(cond,term1,term2)) = 
        let
          fun normalize_ITE (ITE(T,term,_)) = term
            | normalize_ITE (ITE(F,_,term)) = term
            | normalize_ITE (ITE(cond,term1,term2)) = 
              if(term1 = term2) then
                term1
              else
                ITE(cond,term1,term2)
           | normalize_ITE (term) = term
          val cond_n = normalize(cond)
          val term1_n = normalize(term1)
          val term2_n = normalize(term2)
        in
          normalize_ITE(ITE(cond_n,term1_n,term2_n))
        end
      | normalize (IZ(Z)) = T
      | normalize (GTZ(Z)) = F
      | normalize (IZ(term)) = 
        let
          fun normalize_IZ(P(term)) = 
              if(normalize_IZ(term)=T orelse normalize_IZ(term)=F) then
                F
              else
                IZ(P(term))
            | normalize_IZ(S(term)) = 
              if(normalize_IZ(term)=T orelse normalize_IZ(term)=F) then
                F
              else
                IZ(S(term))
            | normalize_IZ(Z) = T
            | normalize_IZ(value) = IZ(value)
          val term_n = normalize(term)
        in
          normalize_IZ(term_n)
        end
      | normalize (GTZ(term)) =
        let
          fun normalize_GTZ(S(term)) = 
              if(term = Z orelse normalize_GTZ(term) = T) then
                T
              else
                GTZ(S(term))
            | normalize_GTZ(P(term)) = 
              if(term = Z orelse normalize_GTZ(term) = F) then
                F
              else
                GTZ(P(term))
            | normalize_GTZ(Z) = F
            | normalize_GTZ(value) = GTZ(value)
          val term_n = normalize(term)
        in
          normalize_GTZ(term_n)
        end
      | normalize(Z) = Z
      | normalize(T) = T
      | normalize(F) = F
      | normalize(S(term)) = 
        let
          fun normalize_S(P(term)) = term
          | normalize_S(term) = S(term)
          val term_n = normalize(term)
        in
          normalize_S(term_n)
        end
      | normalize(P(term)) = 
        let
          fun normalize_P(S(term)) = term
          | normalize_P(term) = P(term)
          val term_n = normalize(term)
        in
          normalize_P(term_n)
        end
      | normalize(VAR(x)) = VAR(x)
end
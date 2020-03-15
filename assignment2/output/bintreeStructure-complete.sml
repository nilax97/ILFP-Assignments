signature BINTREE = 
sig
        datatype 'a bintree = 
                Empty 
                | Node of 'a * 'a bintree * 'a bintree
        datatype 'a option = NONE | SOME of 'a
        exception Empty_bintree;
        exception InvalidTraversal;
        val preorder : 'a bintree ->  'a option list
        val postorder : 'a bintree -> 'a option list
        val inorder : 'a bintree -> ('a option * int) list
        val inorderInverse : ('a option * int) list -> 'a bintree
        val checkTrees : ''a bintree * ''a bintree -> bool
end
structure Bintree : BINTREE = 
struct
            datatype 'a bintree = 
                    Empty 
                    | Node of 'a * 'a bintree * 'a bintree
            datatype 'a option = NONE | SOME of 'a
    
    exception Empty_bintree
        exception InvalidTraversal
        
            local 
                fun pre(Empty, Llist) = NONE::Llist
                        | pre(Node(N,Ltree, Rtree),Llist) = 
                        let
                                val Mlist = pre(Rtree,Llist)
                                val Nlist = pre(Ltree,Mlist)
                        in
                                SOME N :: Nlist
                        end
                in 
                        fun preorder T = pre(T,[])
                end
            local 
                fun post(Empty, Llist) = NONE::Llist
                        | post(Node(N,Ltree, Rtree),Llist) = 
                        let
                                val Mlist = post(Rtree,SOME N::Llist)
                                val Nlist = post(Ltree,Mlist)
                        in
                                Nlist
                        end
                in 
                        fun postorder T = post(T,[])
                end
                local 
                fun ino(Empty, Llist,i) = (NONE,i)::Llist
                        | ino(Node(N,Ltree, Rtree),Llist,i) = 
                        let
                                val Mlist = ino(Rtree,Llist,i+1)
                                val Nlist = ino(Ltree,(SOME N,i)::Mlist,i+1)
                        in
                                Nlist
                        end
                in 
                        fun inorder T = ino(T,[],0)
                end
        local
                fun  Nodify[] = []
                            | Nodify (h::t) = 
                            Node(h,Empty,Empty)::Nodify(t)
                            fun joinNodes(T1 as Node((v1,h1),_,_), T2 as Node((v2,h2),_,_), T3 as Node((v3,h3),_,_)) =
                            if(h1=h3 andalso (h1-1)=h2) then
                                    [Node((v2,h2),T1,T3)]
                            else
                                    [T1,T2,T3]
                            | joinNodes(T1,T2,T3) = raise InvalidTraversal
                    fun combineIter(h1::h2::h3::[]) = 
                                    joinNodes(h1,h2,h3)
                            | combineIter(L as h1::h2::h3::tl) = 
                            let
                                    val M = joinNodes(h1,h2,h3) @ tl
                            in
                                    List.hd(M) :: combineIter(List.tl(M))
                            end
                            | combineIter (L as h1::h2::[]) = L
                            | combineIter L = raise InvalidTraversal
                            fun combine(hd::[]) = hd
                            | combine L =  
                            let
                                    val M = combineIter L
                            in
                                    combine M
                            end
                            fun treeClean(Node((SOME v,_),Ltree,Rtree)) = 
                            let
                                    val LClean = treeClean(Ltree)
                                    val RClean = treeClean(Rtree)
                            in
                                    Node(v, LClean, RClean)
                            end
                            | treeClean(T) = Empty
        in
            fun inorderInverse(L) = 
                            treeClean (combine (Nodify L))

            end
        local
                        fun checkList([],[]) = true
                                    | checkList([],_) = false
                                    | checkList(_,[]) = false
                                    | checkList(NONE::t1, NONE::t2) = checkList(t1,t2)
                                    | checkList(SOME h1::t1, SOME h2::t2) = 
                                    if(h1=h2) then
                                            checkList(t1,t2)
                                    else
                                            false
                                    | checkList(_,_) = false
            in
                    fun checkTrees(T1,T2) = 
                    let
                            val pre1 = preorder(T1)
                            val pre2 = preorder(T2)
                            val pos1 = postorder(T1)
                            val pos2 = postorder(T2)
                    in
                            if(checkList(pre1,pre2) andalso checkList(pos1,pos2)) then
                                    true
                            else
                                    false
                    end
            end
end

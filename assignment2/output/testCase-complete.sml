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
open Bintree;

local
        val t7 = Node (7, Empty, Empty);
        val t6 = Node (6, t7, Empty);
        val t5 = Node (5, Empty, Empty);
        val t4 = Node (4, Empty, Empty);
        val t3 = Node (3, t5, t6);
        val t2 = Node (2, Empty, t4);
in
        val test1 = Node (1, t2, t3);
end
local
        val t15 = Node (15, Empty, Empty);
        val t14 = Node (14, Empty, Empty);
        val t13 = Node (13, Empty, Empty);
        val t12 = Node (12, Empty, Empty);
        val t11 = Node (11, Empty, Empty);
        val t10 = Node (10, Empty, Empty);
        val t9 = Node (9, Empty, Empty);
        val t8 = Node (8, Empty, Empty);
        val t7 = Node(7, t14, t15);
        val t6 = Node (6, t12, t13);
        val t5 = Node (5, t10, t11);
        val t4 = Node (4, t8, t9);
        val t3 = Node (3, t6, t7);
        val t2 = Node (2, t4, t5);
in
        val test2 = Node (1, t2, t3);
end
local
        val t11 = Node (11, Empty, Empty);
        val t10 = Node (10, Empty, Empty);
        val t9 = Node (9, Empty, Empty);
        val t8 = Node (8, Empty, Empty);
        val t5 = Node (5, t10, t11);
        val t4 = Node (4, t8, t9);
        val t2 = Node (2, t4, t5);
in
        val test3 = Node (1, t2, Empty);
end

local
        val t15 = Node (15, Empty, Empty);
        val t14 = Node (14, Empty, Empty);
        val t13 = Node (13, Empty, Empty);
        val t12 = Node (12, Empty, Empty);
        val t7 = Node(7, t14, t15);
        val t6 = Node (6, t12, t13);
        val t3 = Node (3, t6, t7);
in
        val test4 = Node (1, Empty, t3);
end
local
        val t4 = Node (4, Empty, Empty);
        val t3 = Node (3, t4, Empty);
        val t2 = Node (2, t3, Empty);
in
        val test5 = Node (1, t2, Empty);
end

local
        val t4 = Node (4, Empty, Empty);
        val t3 = Node (3, Empty, t4);
        val t2 = Node (2, Empty, t3);
in
        val test6 = Node (1, Empty, t2);
end
local
        val t7 = Node (7, Empty, Empty);
        val t6 = Node (6, Empty, Empty);
        val t5 = Node (5, Empty, t7);
        val t4 = Node (4, t6, Empty);
        val t3 = Node (3, Empty, t5);
        val t2 = Node (2, t4, Empty);
in
        val test7 = Node (1, t2, t3);
end
local
        val t7 = Node (7, Empty, Empty);
        val t6 = Node (6, Empty, Empty);
        val t5 = Node (5, Empty, t7);
        val t4 = Node (4, t6, Empty);
        val t3 = Node (3, t5, Empty);
        val t2 = Node (2, Empty, t4);
in
        val test8 = Node (1, t2, t3);
end
val test1_check = checkTrees(inorderInverse(inorder(test1)),test1);
val test2_check = checkTrees(inorderInverse(inorder(test2)),test2);
val test3_check = checkTrees(inorderInverse(inorder(test3)),test3);
val test4_check = checkTrees(inorderInverse(inorder(test4)),test4);
val test5_check = checkTrees(inorderInverse(inorder(test5)),test5);
val test6_check = checkTrees(inorderInverse(inorder(test6)),test6);
val test7_check = checkTrees(inorderInverse(inorder(test7)),test7);
val test8_check = checkTrees(inorderInverse(inorder(test8)),test8);

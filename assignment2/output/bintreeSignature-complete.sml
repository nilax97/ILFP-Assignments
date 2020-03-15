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

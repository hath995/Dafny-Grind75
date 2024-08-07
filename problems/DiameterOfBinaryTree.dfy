//https://leetcode.com/problems/diameter-of-binary-tree/description/

/*
function diameter(node: TreeNode | null): [number, number] {
  if(node == null) {
    return [-1,-1];
  }
  if(node.left == null && node.right == null) {
    return [0, 0];
  }
  let leftDiameter = diameter(node.left);
  let rightDiameter = diameter(node.right);
  let height = Math.max(leftDiameter[0],rightDiameter[0]) + 1;
  let dim = leftDiameter[0]+rightDiameter[0]+2;
  let maxDiameter = Math.max(leftDiameter[1], rightDiameter[1], dim);
  return [height, maxDiameter];
}

function diameterOfBinaryTree(root: TreeNode | null): number {
  return diameter(root)[1];
};
*/
module TreeDiameter {
//      //Definitions
    datatype Tree = Node(val: int, left: Tree, right: Tree) | Nil


    function reverse<A>(x: seq<A>): seq<A> 
    {
        if x == [] then [] else reverse(x[1..])+[x[0]]
    }

    lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
        ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
    {
        // reveal Reverse();
        if |xs| == 0 {
        assert xs + ys == ys;
        } else {
        assert xs + ys == [xs[0]] + (xs[1..] + ys);
        }
    }

    lemma ReverseIndexAll<T>(xs: seq<T>)
        ensures |reverse(xs)| == |xs|
        ensures forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1]
    {
    }
    predicate distinct<A(==)>(s: seq<A>) {
        forall x,y :: x != y && 0 <= x <= y < |s| ==> s[x] != s[y]
    }

    lemma distincts<A>(xs: seq<A>, ys: seq<A>)
        requires distinct(xs)
        requires distinct(ys)
        requires forall x :: x in xs ==> x !in ys 
        requires forall y :: y in ys ==> y !in xs 
        ensures distinct(xs+ys)
    {
        var len := |xs + ys|;
        forall x,y | x != y && 0 <= x <= y < |xs+ys| 
            ensures (xs+ys)[x] != (xs+ys)[y] 
        {
            if 0 <= x < |xs| && 0 <= y < |xs| {
                assert (xs+ys)[x] != (xs+ys)[y];
            }else if |xs| <= x < |xs+ys| && |xs| <= y < |xs+ys| {
                assert (xs+ys)[x] != (xs+ys)[y];

            }else if 0 <= x < |xs| && |xs| <= y < |xs+ys| {
                notInNotEqual(ys, xs[x]);
                assert (xs+ys)[x] != (xs+ys)[y];
            }
        }

    }

    lemma reverseDistinct<A>(list: seq<A>)
        requires distinct(list)
        ensures distinct(reverse(list))
    {
        ReverseIndexAll(list);
    }
    lemma ReverseSingle<A>(xs: seq<A>) 
        requires |xs| == 1
        ensures reverse(xs) == xs
    {

    }
    lemma reverseReverseIdempotent<A>(xs: seq<A>) 
        ensures reverse(reverse(xs)) == xs
    {
        if xs == [] {

        }else{
            calc {
                reverse(reverse(xs));
                reverse(reverse([xs[0]] + xs[1..]));
                == {ReverseConcat([xs[0]] , xs[1..]);}
                reverse(reverse(xs[1..]) + reverse([xs[0]]));
                == {ReverseSingle([xs[0]]);}
                reverse(reverse(xs[1..]) + [xs[0]]);
                == {ReverseConcat(reverse(xs[1..]), [xs[0]]);}
                reverse([xs[0]]) + reverse(reverse(xs[1..]));
                [xs[0]] + reverse(reverse(xs[1..]));
                == {reverseReverseIdempotent(xs[1..]);}
                xs;
            }
        }
        /* Alternatively */
        // ReverseIndexAll(reverse(xs));
        // ReverseIndexAll(xs);
        // SeqEq(reverse(reverse(xs)), xs);
    }
 lemma notInNotEqual<A>(xs: seq<A>, elem: A)
        requires elem !in xs
        ensures forall k :: 0 <= k < |xs| ==> xs[k] != elem
    {

    }
    lemma distinctSplits<A>(list: seq<A>)
        requires distinct(list)
        ensures forall i :: 1 <= i < |list| ==> distinct(list[..i])
    {}

    function max(left: int, right: int): int {
        if left > right then left else right
    }

    function TreeSet(root: Tree): set<Tree> {
        match root {
            case Nil => {}
            case Node(val, left, right) => {root}+TreeSet(left)+TreeSet(right)
        }
    }

    function TreeHeight(root: Tree): int 
        ensures TreeHeight(root) >= -1
    {
        if root == Nil then -1 else if root.left == Nil && root.right == Nil then 0 else max(TreeHeight(root.left), TreeHeight(root.right)) + 1
    }

    predicate isChild(a: Tree, b: Tree) {
        a != Nil && (a.left == b || a.right == b)
    }

    predicate isParentOrChild(a: Tree, b: Tree) {
        //a != Nil && b != Nil && (a.left == b || a.right == b || (a == b.left || a == b.right))
        a != Nil && b != Nil && (isChild(a, b) || isChild(b, a))
    }

    predicate isTreePath(path: seq<Tree>, start: Tree, end: Tree) {
        if |path| == 0 then false else if |path| == 1 then start != Nil && start == end && path[0] == start else match path[0] {
            case Nil => false
            case Node(val, left, right) => path[0] == start && path[|path|-1] == end && isParentOrChild(path[0], path[1]) && isTreePath(path[1..], path[1], end)
        }
    }

    predicate isTreePathAlt(path: seq<Tree>, start: Tree, end: Tree) {
        if |path| == 0 then false else if |path| == 1 then start != Nil && start == end && path[0] == start else path[0] == start && start != Nil && end == path[|path|-1] == end && forall i :: 0 <= i < |path| - 1 ==> isParentOrChild(path[i], path[i+1])
    }

    predicate isDescTreePath(path: seq<Tree>, start: Tree, end: Tree) {
        if |path| == 0 then false else if |path| == 1 then match path[0] {
                case Nil => false
                case Node(val, left, right) => path[0] == start && end == start
        } else match path[0] {
            case Nil => false
            case Node(val, left, right) => end != Nil && path[|path|-1] == end && path[0] == start && path[1] != Nil && ((left == path[1] && isDescTreePath(path[1..],left, end)) || (right == path[1] && isDescTreePath(path[1..], right, end)))
        }
    }

    predicate isAscTreePath(paths: seq<Tree>, start: Tree, end: Tree) {
        if |paths| == 0 then 
            false 
        else if |paths| == 1 then match paths[0] {
            case Nil => false
            case Node(val, left, right) => start == paths[0] && end == start
        } else match paths[0] {
            case Nil => false
            case Node(val, left, right) => end != Nil && paths[|paths|-1] == end && start == paths[0] && paths[1] != Nil  && ((paths[0] == paths[1].left && isAscTreePath(paths[1..], paths[1], end)) || (paths[0] == paths[1].right && isAscTreePath(paths[1..], paths[1], end)))
        }
    }

    predicate isAscTreePathAlt(path: seq<Tree>, start: Tree, end: Tree) {
        if |path| == 0 then false else if |path| == 1 then start != Nil && start == end && path[0] == start else path[0] == start && start != Nil && end == path[|path|-1] && forall i :: 0 <= i < |path| -1 ==> isChild(path[i+1], path[i])
    }

    lemma AscTreePathAreTheSame(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil && end != Nil
        requires isAscTreePath(path, start, end)
        ensures isAscTreePathAlt(path, start, end)
    {
        AscTreePathNotNil(path, start, end);
    }

    lemma AscTreePathAreTheSameAlt(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil && end != Nil
        requires isAscTreePathAlt(path, start, end)
        ensures isAscTreePath(path, start, end)
    {
        // AscTreePathNotNil(path, start, end);
    }
    

    ghost predicate ChildrenAreSeparate(root: Tree) {
        root == Nil || (root != Nil && (TreeSet(root.left) !! TreeSet(root.right)) && ChildrenAreSeparate(root.left) && ChildrenAreSeparate(root.right))
    }

    predicate isValidPath(path: seq<Tree>, root: Tree) {
        forall node :: node in path ==> node in TreeSet(root)
    }

    ghost predicate isPath(path: seq<Tree>, start: Tree, end: Tree, root: Tree) {
        isTreePath(path,start, end) && isValidPath(path, root) && distinct(path)
    }

    predicate isLeaf(node: Tree ) {
        node != Nil && node.right == Nil && node.left == Nil
    }

//     //lemmas



    lemma TreeHeightMax(root: Tree) 
        ensures forall node :: node in TreeSet(root) ==> TreeHeight(root) >= TreeHeight(node)
    {}

    lemma TreePathsAreTheSameAlt(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires isTreePath(path, start, end)
        ensures isTreePathAlt(path, start, end)
    {

    }
    
    lemma TreePathSplit(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isTreePathAlt(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isTreePath(path[..i], start, path[i-1])
    {
        TreePathSplitAlt(path, start, end);
        TreePathsAreTheSame(path, start, end);
        TreePathNotNil(path, start, end);
        forall i | 1 <= i < |path| 
            ensures isTreePath(path[..i], start, path[i-1])
        {
            TreePathChildrenAlt(path[..i], start, path[i-1]);
        }
    }

    lemma TreePathSplitAlt(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        // requires end != Nil
        requires |path| > 1
        requires isTreePathAlt(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isTreePathAlt(path[..i], start, path[i-1])
    {}

    lemma TreePathsAreTheSame(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires isTreePathAlt(path, start, end)
        ensures isTreePath(path, start, end)
    {}
    
    lemma TreePathsReverseAreTreePaths(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires isTreePath(path, start, end)
        ensures isTreePath(reverse(path), end, start)
    {
        TreePathsAreTheSameAlt(path, start, end);
        ReverseIndexAll(path);
        forall i | 0 <= i < |path| - 1
            ensures isParentOrChild(reverse(path)[i], reverse(path)[i+1]) 
        {

        }
        TreePathsAreTheSame(reverse(path), end, start);
    }

    lemma DescPathChildren(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isDescTreePath(path, start, end)
        ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
    {}

    lemma DescPathChildrenAlt(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 0
        requires path[0] == start
        requires path[|path|-1] == end
        requires forall i :: 0 <= i < |path| ==> path[i] != Nil
        requires forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
        ensures isDescTreePath(path, start, end)
    {}

    lemma DescPathChildrenTreeSet(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 0
        requires isDescTreePath(path, start, end)
        ensures isValidPath(path, start)
    {
        if |path| == 1 {
            assert path[0] == end;
        }else{
            // assert path == path[..|path|-1]+[end];
            assert path == [start]+path[1..];
            DescPathChildren(path, start, end);
        }
    }

    lemma TreePathChildrenAlt(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires path[0] == start;
        requires path[|path|-1] == end;
        requires forall i :: 0 <= i < |path| ==> path[i] != Nil
        requires forall i :: 0 <= i < |path| - 1 ==> isParentOrChild(path[i], path[i+1])
        ensures isTreePath(path, start, end)
    {}

    lemma DescPathChildrenReverse(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isDescTreePath(path, start, end)
        ensures forall i :: 0 <= i < |reverse(path)| - 1 ==> isChild(reverse(path)[i+1], reverse(path)[i])
    {
        DescPathChildren(path, start, end);
        ReverseIndexAll(path);
    }

    lemma AscPathChildrenAlt(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires path[0] == start;
        requires path[|path|-1] == end;
        requires forall i :: 0 <= i < |path| - 1 ==> isChild(path[i+1], path[i])
        ensures isAscTreePath(path, start, end)
    {}

    lemma AscPathChildren(path: seq<Tree>, start: Tree, end: Tree)
        // requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isAscTreePath(path, start, end)
        ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i+1], path[i])
    {}

    lemma AscPathChildrenTreeSet(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 0
        requires isAscTreePath(path, start, end)
        ensures isValidPath(path, end)
    {
        if |path| == 1 {
            assert path[0] == end;
        }else{
            assert path == path[..|path|-1]+[end];
            AscPathChildren(path, start, end);
            assert start == path[..|path|-1][0];
            AscTreePathSplit(path, start, end);
            // assert isAscTreePath(path[..|path|-1], start, path[|path|-2]);
        }
    }
    
    lemma AscTreePathSplitAlt(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        // requires end != Nil
        requires |path| > 1
        requires isAscTreePathAlt(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isAscTreePathAlt(path[..i], start, path[i-1])
    {}

    lemma AscTreePathSplit(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isAscTreePath(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isAscTreePath(path[..i], start, path[i-1])
    {
        AscTreePathAreTheSame(path, start, end);
        AscTreePathSplitAlt(path, start, end);
        AscTreePathNotNil(path, start, end);
        forall i | 1 <= i < |path| 
            ensures isAscTreePath(path[..i], start, path[i-1])
        {
            assert path[i-1] in path;
            AscTreePathAreTheSameAlt(path[..i], start, path[i-1]);
        }
    }


    lemma TreeSetChildInTreeSet(root: Tree, child: Tree) 
        requires root != Nil
        requires child != Nil && child in TreeSet(root)
        ensures TreeSet(child) <= TreeSet(root)
    {}

    lemma parentNotInTreeSet(parent: Tree, root: Tree)
        requires parent != Nil && parent != root && (parent.left == root || parent.right == root)
        ensures parent !in TreeSet(root)
    {
        if root == Nil {} else {
            assert TreeSet(root) == {root}+TreeSet(root.left)+TreeSet(root.right);
            parentNotInTreeSet(root, root.left);
            parentNotInTreeSet(root, root.right);
            if parent in TreeSet(root.left) {
                TreeSetChildInTreeSet(root.left, parent);
            }else if parent in TreeSet(root.right) {
                TreeSetChildInTreeSet(root.right, parent);
            }
        }
    }

    lemma childrenInTreeSet(root: Tree, child: Tree, path: seq<Tree>)
        requires root != Nil && child != Nil
        requires child in TreeSet(root)
        requires isValidPath(path, child)
        ensures isValidPath(path, root)
    {}

    lemma validChildrenAlt(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires path[0] == start;
        requires path[|path|-1] == end;
        requires forall i :: 0 <= i < |path| ==> path[i] != Nil
        requires forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
        requires forall i :: 0 <= i < |path| - 1 ==> path[i+1] in TreeSet(path[i+1])
        ensures forall i :: 0 <= i < |path| - 1 ==> isValidPath(path[i..], path[i])
    {
        if |path| == 2 {
            assert isValidPath(path[0..], path[0]);
            // assert isValidPath(path[1..], path[1]);
            assert forall i :: 0 <= i < |path| - 1 ==> isValidPath(path[i..], path[i]);
            // assert start in path && end in path;
        }else{
            validChildrenAlt(path[1..], path[1], end);
        }
    }

    lemma isDescPathAndValidImpliesAllValid(path: seq<Tree>, start: Tree, end: Tree) 
        requires isDescTreePath(path, start, end)
        requires isValidPath(path, start)
        requires |path| > 1
        ensures forall i :: 0 <= i < |path| ==> isValidPath(path[i..], path[i]);
    {
        // assert path[1] in TreeSet(start);
        // assert isDescTreePath(path[1..], path[1], end);
        // assert isValidPath(path[1..], start);
        DescTreePathNotNil(path, start, end);
        DescPathChildren(path, start, end);
        assert forall i :: 0 <= i < |path| ==> path[i] in path;
        validChildrenAlt(path, start, end);
    }

    lemma DescPathIsAscPath(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires isDescTreePath(path, start, end)
        ensures isAscTreePath(reverse(path), end, start)
    {
        DescTreePathNotNil(path, start, end);
        ReverseIndexAll(path);
        if |path| == 1 {} else {
            DescPathChildrenReverse(path, start, end);
            AscPathChildrenAlt(reverse(path), end, start);
        }
    }

    lemma AscTreePathNotNil(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires isAscTreePath(path, start, end)
        ensures forall node :: node in path ==> node != Nil
    {
        if |path| == 1 {
        }else if |path| > 1 {
            assert path == [path[0]]+path[1..];
            AscTreePathNotNil(path[1..], path[1], end);
        }
    }

    lemma AscPathChildrenReverse(path: seq<Tree>, start: Tree, end: Tree)
        // requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isAscTreePath(path, start, end)
        ensures forall i :: 0 <= i < |reverse(path)| - 1 ==> isChild(reverse(path)[i], reverse(path)[i+1])
    {
        AscPathChildren(path, start, end);
        ReverseIndexAll(path);
    }

    lemma AscPathIsDescPath(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires isAscTreePath(path, start, end)
        ensures isDescTreePath(reverse(path), end, start)
    {
        AscTreePathNotNil(path, start, end);
        ReverseIndexAll(path);
        if |path| == 1 {

        }else{
            AscPathChildrenReverse(path, start, end);
            assert forall i :: 0 <= i < |reverse(path)| ==> reverse(path)[i] in path && reverse(path)[i] != Nil;
            DescPathChildrenAlt(reverse(path), end, start);
        }
    }

    lemma DescTreePathToPath(path: seq<Tree>, root: Tree, end: Tree)
        requires root != Nil
        requires end != Nil
        requires isDescTreePath(path, root, end)
        ensures isTreePath(path, root, end)
    {
        assert path[0] == root;
        assert path[|path|-1] == end;
        if |path| == 1 {
            assert path == [root];
            // assert isDescTreePath([root], root, end);
            assert root == end;
            // assert isTreePath([root], root, end);
        }
    }

    lemma AscTreePathToPath(path: seq<Tree>, root: Tree, end: Tree)
        requires root != Nil
        requires end != Nil
        requires isAscTreePath(path, root, end)
        ensures isTreePath(path, root, end)
    {
        assert path[0] == root;
        assert path[|path|-1] == end;
        if |path| == 1 {
            assert path == [root];
            // assert isAscTreePath([root], root, end);
            assert root == end;
            // assert isTreePath([root], root, end);
        }
    }

    lemma DescTreePathNotNil(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires isDescTreePath(path, start, end)
        ensures forall node :: node in path ==> node != Nil
        ensures forall i :: 0 <= i < |path| ==> path[i] != Nil
    {
        if |path| == 1 {
        }else if |path| > 1 {
            assert path == [path[0]]+path[1..];
            DescTreePathNotNil(path[1..], path[1], end);
        }
    }

    lemma TreePathNotNil(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires |path| >= 1
        requires isTreePath(path, start, end)
        ensures forall node :: node in path ==> node != Nil
        ensures forall i :: 0 <= i < |path| ==> path[i] != Nil
    {
        if |path| == 1 {
        }else if |path| > 1 {
            assert path == [path[0]]+path[1..];
            TreePathNotNil(path[1..], path[1], end);
        }
    }

    lemma TreePlusTree(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
        requires start != Nil && root != Nil && end != Nil
        requires start != root && root != end
        requires isTreePath(path, start, root)
        requires isTreePath(pathtwo, root, end)
        ensures isTreePath(path + pathtwo[1..], start, end)
        ensures |path + pathtwo[1..]| == |path|+|pathtwo|-1
    {
        TreePathsAreTheSameAlt(path, start, root);
        TreePathsAreTheSameAlt(pathtwo, root, end);
        assert isTreePathAlt(path + pathtwo[1..], start, end);
        TreePathsAreTheSame(path + pathtwo[1..], start, end);
    }

    lemma DescPlusAsc(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
        requires start != Nil && root != Nil && end != Nil
        requires start != root && root != end
        requires isDescTreePath(path, root, end)
        requires isAscTreePath(pathtwo, start, root)
        ensures isTreePath(pathtwo + path[1..], start, end)
    {
        var result := pathtwo + path[1..];
        assert result[0] == start;
        DescTreePathToPath(path, root, end);
        AscTreePathToPath(pathtwo, start, root);
        TreePlusTree(pathtwo, start, root, path, end);
        assert |pathtwo + path[1..]| == |pathtwo| + |path| -1;
    }

    lemma DescPlusDesc(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
        requires start != Nil && root != Nil && end != Nil
        requires start != root && root != end
        requires isDescTreePath(path, root, end)
        requires isDescTreePath(pathtwo, root, start)
        ensures isTreePath(reverse(pathtwo) + path[1..], start, end)
    {
        DescPathIsAscPath(pathtwo, root, start);
        // assert isAscTreePath(reverse(pathtwo), start, root);
        DescPlusAsc(path, start, root, reverse(pathtwo), end);
    }


    lemma isPathSlices(path: seq<Tree>, start: Tree, end: Tree, root: Tree) 
        requires |path| >= 1
        requires isPath(path, start, end, root)
        ensures forall i :: 0 < i < |path| ==> isPath(path[..(i+1)], start, path[i], root) && isPath(path[i..], path[i], end, root)
    {
        TreePathNotNil(path, start, end);
        TreePathsAreTheSameAlt(path, start, end);
        forall i | 0 < i < |path| 
            ensures isPath(path[..(i+1)], start, path[i], root) && isPath(path[i..], path[i], end, root)
        {
            assert path == path[..i]+path[i..];
            TreePathChildrenAlt(path[..(i+1)], start, path[i]);
            TreePathChildrenAlt(path[i..], path[i], end);
            assert isValidPath(path[..i], root);
            assert isValidPath(path[i..], root);
            // assert distinct(path[..i]);
            // assert distinct(path[i..]);
        }
    }


    lemma TreePathStartingAtRootIsChildSeries(root: Tree, start: Tree, end: Tree, path: seq<Tree>) 
        requires root != Nil && end != Nil
        requires |path| > 1
        requires isPath(path, root, end, root)
        requires root in path && root == start;
        ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
    {
        TreePathNotNil(path, start, end);
        assert [root] == path[..1];
        TreePathsAreTheSameAlt(path, root, end);
        forall k: nat | k < 1
            ensures isChild(path[k], path[k+1])
        {
            // assert isParentOrChild(path[k], path[k+1]);
            if isChild(path[k+1], path[k]) {
                parentNotInTreeSet(path[k+1], root);
            }
        }
        DescPathAccumulatesParents(path,[root], 1, {root}, root, end);
    }

    lemma DescPathAccumulatesParents(path: seq<Tree>, pathSub: seq<Tree>,  i: nat, parentset: set<Tree>, root: Tree, end: Tree)
        requires |path| >= 1
        requires 1 <= i < |path|
        requires isTreePath(path, root, end)
        requires forall k:nat :: k < |path| ==> path[k] != Nil 
        requires forall k: nat :: k < i ==> path[k] in parentset
        requires forall k: nat :: k < i ==> isChild(path[k], path[k+1])
        requires distinct(path)
        requires pathSub == path[..i] && |pathSub| >= 1
        requires isDescTreePath(pathSub, root, path[i-1])
        requires i < |path|-1 ==> isParentOrChild(path[i], path[i+1])
        requires root == path[0];
        ensures i < |path|-1 ==> isChild(path[i], path[i+1])
        ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
        decreases |path|-i
    {
        if i < |path|-1 {
            TreePathsAreTheSameAlt(path, root, end);
            if isChild(path[i+1], path[i]) {
                // assert isChild(path[i-1], path[i]);
                parentsAreTheSame(path[i+1], path[i-1], path[i]);
                assert false;
            }else if isChild(path[i], path[i+1]) {
                if |pathSub| == 1 {

                }else{
                DescPathChildren(pathSub, root, path[i-1]);
                DescPathChildrenAlt(pathSub+[path[i]], root, path[i]);
                }
                assert isDescTreePath(pathSub+[path[i]], root, path[i]);
                DescPathAccumulatesParents(path, pathSub+[path[i]], i+1, parentset+{path[i]}, root, end);
            }
        }
    }

    lemma TreePathStartingAtRootIsDesc(path: seq<Tree>, start: Tree, end: Tree, root: Tree) 
        requires root != Nil && end != Nil
        requires isPath(path, start, end, root)
        requires root in path && root == start;
        ensures isDescTreePath(path, start, end)
    {
        if |path| == 1 {
        }else{
            TreePathNotNil(path, start, end);
            TreePathsAreTheSameAlt(path, start, end);
            TreePathSplit(path, start, end);
            TreePathStartingAtRootIsChildSeries(root, start, end, path);
            DescPathChildrenAlt(path, start, end);
        }
    }

    lemma descRoot(root: Tree, start: Tree, end: Tree, path: seq<Tree>) 
        requires isDescTreePath(path, start, end)
        requires isValidPath(path, root)
        requires root in path
        ensures start == root
    {
        if start == root {

        }else {
            assert path[0] != root;
            assert path == [path[0]]+path[1..];
            assert root in path[1..];
            DescPathChildren(path, start, end);
            var i :| 0 < i< |path| && path[i] == root;
            // assert isChild(path[i-1], root);
            parentNotInTreeSet(path[i-1], root);
            assert false;
        }
    }

    lemma ascRoot(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
        requires isAscTreePath(path, start, end)
        requires isValidPath(path, root)
        requires root in path
        ensures end == root
    {
        if end == root {

        }else {
            assert path[|path|-1] != root;
            AscPathChildren(path,start,end);
            var i :| 0 <= i < |path|-1 && path[i] == root;
            // assert isChild(path[i+1], path[i]);
            parentNotInTreeSet(path[i+1], root);
            assert false;
        }
    }

    lemma TreeHeightToDescTreePath(root: Tree, h: int) 
        requires root != Nil
        requires h == TreeHeight(root)
        ensures exists end: Tree, path: seq<Tree> :: (isLeaf(end) && end in TreeSet(root))  && isDescTreePath(path, root, end) && |path| == h+1 && isValidPath(path, root) && distinct(path)
    {
        if h == 0 {
            assert isDescTreePath([root], root, root);
            assert isValidPath([root], root);
            assert distinct([root]);
            // assert root in TreeSet(root);
        }else if h >= 1 {
            if root.left != Nil && TreeHeight(root.left) == h-1 {
                TreeHeightToDescTreePath(root.left, h-1);
                TreeSetChildInTreeSet(root, root.left);
                var end: Tree, path: seq<Tree> :| isLeaf(end) && end in TreeSet(root.left) && isDescTreePath(path, root.left, end) && |path| == h && isValidPath(path, root.left) && distinct(path);
                assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
                parentNotInTreeSet(root, root.left);
                distincts([root], path);
                assert distinct([root]+path);
                assert isValidPath([root]+path, root);
            } else if root.right != Nil && TreeHeight(root.right) == h-1 {
                TreeHeightToDescTreePath(root.right, h-1);
                TreeSetChildInTreeSet(root, root.right);
                var end: Tree, path: seq<Tree> :| isLeaf(end) && end in TreeSet(root.right) && isDescTreePath(path, root.right, end) && |path| == h && isValidPath(path, root.right) && distinct(path);
                assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
                parentNotInTreeSet(root, root.right);
                distincts([root], path);
                assert distinct([root]+path);
                assert isValidPath([root]+path, root);
            }else {
                assert false;
            }
        }
    }

    lemma parentsAreTheSame(p1: Tree, p2: Tree, child: Tree)
        requires p1 != Nil && p2 != Nil && child != Nil
        requires isChild(p1, child)
        requires isChild(p2, child)
        ensures p1 == p2

    lemma pathStartingAtRootDescSlice(root: Tree, start: Tree, end: Tree, path: seq<Tree>, i: int)
        requires root != Nil
        requires root in path && path[0] == root
        requires ChildrenAreSeparate(root)
        requires isPath(path, start, end, root)
        requires 0 < i <= |path|
        requires isDescTreePath(path[0..i], root, path[i-1])
        requires |path| >= 1
        decreases |path| - i
        ensures isDescTreePath(path, root, end)
    {
        TreePathNotNil(path, start, end);
        TreePathsAreTheSameAlt(path, start,end);
        if i < |path| {
            if isChild(path[i-1], path[i]) {
                if i == 1 {
                    // assert isDescTreePath(path[0..1], root, path[i-1]);
                }else{

                    DescPathChildren(path[0..i], root, path[i-1]);
                }
                DescPathChildrenAlt(path[0..(i+1)], root, path[i]);
                // assert isDescTreePath(path[0..(i+1)], root, path[i]);
                pathStartingAtRootDescSlice(root, start, end, path, i+1);
            }else if isChild(path[i], path[i-1]) {
                if i == 1 {
                    parentNotInTreeSet(path[i],root);
                }else{
                    DescPathChildren(path[0..i], root, path[i-1]);
                    // assert isChild(path[i-2],path[i-1]);
                    parentsAreTheSame(path[i-2], path[i], path[i-1]);
                    // assert path[i-2] == path[i];
                    assert false;
                }
                assert false;
            }else{
                // assert !isParentOrChild(path[i-1], path[i]);
                assert false;
            }
        }else{
            assert i == |path|;
            // assert isDescTreePath(path[0..|path|], root, path[|path|-1]);
            assert path[0..|path|] == path;
        }
    }

    lemma pathStartingAtRootDesc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
        requires root != Nil
        requires root in path && path[0] == root
        requires ChildrenAreSeparate(root)
        requires isPath(path, start, end, root)
        requires |path| >= 1
        decreases |path|
        ensures isDescTreePath(path, root, end)
    {
        if |path| == 1 {

        }else{
            if isChild(path[1], root) {
                parentNotInTreeSet(path[1], root);
                assert false;
            }else if isChild(root, path[1]) {
                assert path[1] == root.left || path[1] == root.right;
                assert isDescTreePath([root, path[1]], root, path[1]);
                pathStartingAtRootDescSlice(root, start, end, path, 1);
            }
        }
    }

    lemma EndDeterminesPath(path: seq<Tree>, start: Tree, end: Tree)
        requires |path| > 1
        requires start != Nil && end != Nil
        requires isDescTreePath(path, start, end)
        requires isValidPath(path, start);
        requires ChildrenAreSeparate(start)
        ensures end in TreeSet(start.left) ==> path[1] == start.left
        ensures end in TreeSet(start.right) ==> path[1] == start.right
    {
        isDescPathAndValidImpliesAllValid(path, start, end);
    }

    lemma RootBounded(root: Tree, h: int) 
        requires root != Nil
        requires TreeHeight(root) == h
        ensures (TreeHeight(root.right) == h-1 && TreeHeight(root.left) <= h-1) || (TreeHeight(root.right) <= h-1 && TreeHeight(root.left) == h-1)
    {}


// method TestPath() {
//     var rootleaf := Node(4, Nil, Nil);
//     var leaf := Node(3, Nil, Nil);
//     var child := Node(2, Nil, leaf);
//     var root := Node(1, child, rootleaf);

//     var test := Node(10, rootleaf, rootleaf);
//     //should this be allowed?
//     assert isTreePath([rootleaf, root, rootleaf], rootleaf, rootleaf);
//     // assert isPath([leaf, child, root, rootleaf]);
//     assert !isTreePath([root, rootleaf], leaf, rootleaf);
//     assert isTreePath([leaf, child, root], leaf, root);
//     assert isTreePath([root, rootleaf], root, rootleaf);
//     assert isTreePath([leaf, child, root, rootleaf], leaf, rootleaf);
//     assert isDescTreePath([root, child, leaf], root, leaf);
//     assert !isDescTreePath([root], root, leaf);
//     assert isDescTreePath([root, rootleaf],root, rootleaf);
//     // assert isTreePath([leaf], leaf, leaf);
//     // assert isTreePath([child], child, child);
//     // assert isTreePath([leaf,child], leaf, child);
//     assert isTreePath([leaf,child,root], leaf, root);
//     assert isTreePath([root,child,leaf], root, leaf);
// }


lemma pathEndingAtRootAsc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path && path[|path|-1] == root && end == root
    // requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires |path| >= 1
    decreases |path|
    ensures isAscTreePath(path, start, root)
{
    if |path| == 1 {
    }else {
        TreePathNotNil(path, start, root);
        TreePathsReverseAreTreePaths(path, start, end);
        ReverseIndexAll(path); 
        TreePathStartingAtRootIsDesc(reverse(path), end, start, root);
        DescPathIsAscPath(reverse(path), root, start);
        // assert isAscTreePath(reverse(reverse(path)), start, root);
        reverseReverseIdempotent(path);
    }
}
// // by a similar argument to pathStartingAtRootDesc
lemma nonAscendingContra(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires path[|path|-1] == root
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    ensures false 
{
    assert end == root;
    if |path| == 1 {
        // assert isAscTreePath(path, start, end);
        assert false;
    }else{
        if isChild(path[|path|-2], path[|path|-1]) {
            parentNotInTreeSet(path[|path|-2], root);
        }else if isChild(path[|path|-1], path[|path|-2]) {
            if |path| == 2 {

            }else{
                TreePathsAreTheSameAlt(path, start, end);
                TreePathSplit(path, start, end);
                distinctSplits(path);
                if isAscTreePath(path[..|path|-1], start, path[|path|-2]) {
                    assert path == path[..|path|-1]+[root];
                    AscTreePathNotNil(path[..|path|-1], start, path[|path|-2]);
                    AscTreePathAreTheSame(path[..|path|-1], start, path[|path|-2]);
                    assert isAscTreePathAlt(path, start, root);
                    AscTreePathAreTheSameAlt(path,start, root);
                    // assert isAscTreePath(path, start, root);
                    assert false;
                } else if isDescTreePath(path[..|path|-1], start, path[|path|-2]) {
                    DescPathChildren(path[..|path|-1], start, path[|path|-2]);
                    // assert isChild(path[|path|-3], path[|path|-2]); 
                    parentsAreTheSame(path[|path|-3], root, path[|path|-2]);
                    // assert path[|path|-3] == root;
                    // assert !distinct(path);
                    assert false;
                }else{
                    if isValidPath(path[..|path|-1], path[|path|-2]) {
                        nonAscendingContra(path[|path|-2], start, path[|path|-2], path[..|path|-1]);
                    }else{
                        var nextRoot :=path[|path|-2];
                        // assert TreeSet(nextRoot) <= TreeSet(root);
                        TreePathsAreTheSameAlt(path, start, end);
                        var badnode: Tree, k: nat :| badnode in path[..|path|-1] && badnode !in TreeSet(nextRoot) && badnode in TreeSet(root) && k < |path|-2 && path[k] == badnode;
                        TreePathNotNil(path,start,end);
                        /*
                            Basically either the path is disconnected or root is in the path twice
                            We have some path in the alternate branch but it isn't connected
                        */
                        // forall i | 0 <= i < |path| - 1 
                        //     ensures isParentOrChild(path[i], path[i+1]) 
                        // {
                        //     assert isParentOrChild(path[i], path[i+1]);
                        // }
                        if nextRoot == root.left {
                            // assert badnode in TreeSet(root.right);
                            nonAscendingContraHelpLeft(root, start, end, path, k, |path|-2, badnode);
                            assert false;
                        }else if nextRoot == root.right {
                            // assert badnode in TreeSet(root.left);
                            nonAscendingContraHelpRight(root, start, end, path, k, |path|-2, badnode);
                            assert false;
                        }else {
                            assert false;
                        }
                    }
                }
            }
        }else{
            assert !isParentOrChild(path[|path|-2], path[|path|-1]);
            assert path == path[..|path|-2]+[path[|path|-2], root];
            TreePathsAreTheSameAlt(path, start, end);
            assert false;
        }

    }
}
 
lemma nonAscendingContraHelpRight(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: nat, i: nat, badnode: Tree)
    requires |path| > 2
    requires root != Nil
    requires root in path
    requires forall node :: node in path ==> node != Nil
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isTreePathAlt(path, start, end)
    requires path[|path|-1] == root
    requires isChild(path[|path|-1], path[|path|-2])
    requires root.right == path[|path|-2]
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    requires !isValidPath(path[..|path|-1], path[|path|-2])
    requires k < i <= |path|-2
    requires path[i] in TreeSet(root.right)
    requires badnode in path[..|path|-1]
    requires badnode !in TreeSet(root.right) && badnode !in TreeSet(path[i]) && badnode in TreeSet(root) && badnode in TreeSet(root.left)
    requires k < |path|-2 && path[k] == badnode
    decreases i-k
    ensures false
{
    if root.left == Nil {

    }else{
        assert badnode in path;
        assert path[i] in path;
        TreeSetChildInTreeSet(root.right, path[i]);
        TreeSetChildInTreeSet(root.left, badnode);
        if isChild(badnode, path[k+1]) {
            // assert path[k+1] in TreeSet(badnode);
            TreeSetChildInTreeSet(badnode, path[k+1]);
            // assert path[k+1] in TreeSet(root.left);
            // assert TreeSet(path[i]) <= TreeSet(root.right);
            // assert TreeSet(path[i]) !! TreeSet(path[k+1]);
            nonAscendingContraHelpRight(root, start, end, path, k+1, i, path[k+1]);
        }else if isChild(path[k+1], badnode) {
            if path[k+1] in TreeSet(root.left) {
                nonAscendingContraHelpRight(root, start, end, path, k+1, i, path[k+1]);
            } else if path[k+1] in TreeSet(root) && path[k+1] !in TreeSet(root.left) && path[k+1] !in TreeSet(root.right) {
                // assert path[k+1] == root;
            } else if path[k+1] in TreeSet(root.right) {
                // assert badnode in TreeSet(path[k+1]);
                TreeSetChildInTreeSet(root.right, path[k+1]);
                // assert TreeSet(path[k+1]) <= TreeSet(root.right);
                assert false;
            }else {

            }
        }else{

        }
    }
}

lemma nonAscendingContraHelpLeft(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: nat, i: nat, badnode: Tree)
    requires |path| > 2
    requires root != Nil
    requires root in path
    requires forall node :: node in path ==> node != Nil
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isTreePathAlt(path, start, end)
    requires path[|path|-1] == root
    requires isChild(path[|path|-1], path[|path|-2])
    requires root.left == path[|path|-2]
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    requires !isValidPath(path[..|path|-1], path[|path|-2])
    requires k < i <= |path|-2
    requires path[i] in TreeSet(root.left)
    requires badnode in path[..|path|-1]
    requires badnode !in TreeSet(root.left) && badnode !in TreeSet(path[i]) && badnode in TreeSet(root) && badnode in TreeSet(root.right)
    requires k < |path|-2 && path[k] == badnode
    decreases i-k
    ensures false
{
    if root.left == Nil {

    }else{
        assert badnode in path;
        assert path[i] in path;
        TreeSetChildInTreeSet(root.left, path[i]);
        TreeSetChildInTreeSet(root.right, badnode);
        if k == |path|-3 {
            // assert isParentOrChild(path[k], path[|path|-2]);
            // assert path[k] !in TreeSet(path[|path|-2]);
            // assert isChild(path[k], path[|path|-2]);
            parentsAreTheSame(path[|path|-3], root, path[|path|-2]);
        }else{
            if isChild(badnode, path[k+1]) {
                // assert path[k+1] in TreeSet(badnode);
                TreeSetChildInTreeSet(badnode, path[k+1]);
                // assert pathjj
                // assert TreeSet(path[i]) <= TreeSet(root.left);
                // assert TreeSet(path[i]) !! TreeSet(path[k+1]);
                nonAscendingContraHelpLeft(root, start, end, path, k+1, i, path[k+1]);
            }else if isChild(path[k+1], badnode) {
                if path[k+1] in TreeSet(root.right) {
                    nonAscendingContraHelpLeft(root, start, end, path, k+1, i, path[k+1]);
                } else if path[k+1] in TreeSet(root) && path[k+1] !in TreeSet(root.left) && path[k+1] !in TreeSet(root.right) {
                    // assert path[k+1] == root;
                } else if path[k+1] in TreeSet(root.left) {
                    // assert badnode in TreeSet(path[k+1]);
                    TreeSetChildInTreeSet(root.left, path[k+1]);
                    assert false;
                }else {

                }
            }else{

            }
        }
    }
}

lemma {:vcs_split_on_every_assert} pathOptions(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    decreases |path|
    ensures isAscTreePath(path, start, end) || isDescTreePath(path, start, end) || exists i :: 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end)
{
    if isAscTreePath(path, start, end) {

    } else if isDescTreePath(path, start, end) {

    }else{
        assert !isAscTreePath(path, start, end);
        assert !isDescTreePath(path, start, end);
        if path[0] == root {
            if |path| == 1 {
                assert exists i :: 0 <= i < |path| && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
            }else{
                assert isAscTreePath(path[..(0+1)], start, root);
                pathStartingAtRootDesc(root, start, end, path);
                assert false;
            }
        }else if path[|path|-1] == root {
            // pathEndingAtRootAsc(root,start, end, path);
            nonAscendingContra(root,start, end, path);
            assert false;
        }else{
            assert root in path[1..];
            isPathSlices(path, start, end, root);
            var i :| 0 < i < |path|-1 && path[i] == root;
            // assert path == path[..(i+1)]+path[i+1..];
            assert path[..i+1][|path[..i+1]|-1] == root;
            assert path[i..][0] == root;
            assert isPath(path[..(i+1)], start, path[i], root);
            assert isPath(path[i..], root, end, root);
            pathStartingAtRootDesc(root, path[i], end, path[i..]);
            pathEndingAtRootAsc(root, start, path[i], path[..(i+1)]);
        }
    }
}

lemma {:vcs_split_on_every_assert} pathOptions2(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root !in path
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    decreases |path|
    ensures isAscTreePath(path, start, end) || isDescTreePath(path, start, end) || exists childRoot: Tree, i :: 0 < i < |path|-1 && path[i] == childRoot && isAscTreePath(path[..(i+1)], start, childRoot) && isDescTreePath(path[i..], childRoot, end)
{
    if isAscTreePath(path, start, end) {

    } else if isDescTreePath(path, start, end) {

    }else{
        assert !isAscTreePath(path, start, end);
        assert !isDescTreePath(path, start, end);
        assert |path| > 1;
        if isChild(path[0], path[1]){ 
            //descending
            nonAscendingContra2(root, start, end, path, 2);

        }else{
            //ascending
            assert isChild(path[1], path[0]);
            ChildRootExists(root, start, end, path, 2);
            
        }
        assert exists childRoot: Tree, i :: 0 < i < |path|-1 && path[i] == childRoot && isAscTreePath(path[..(i+1)], start, childRoot) && isDescTreePath(path[i..], childRoot, end);

    }
}

lemma ChildRootExists(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: int)
    requires root != Nil
    requires root !in path
    requires 1 < k <= |path|
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isAscTreePath(path[..k], start, path[k-1])
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    decreases |path|-k
    ensures exists childRoot: Tree, i :: 0 < i < |path|-1 && path[i] == childRoot && isAscTreePath(path[..(i+1)], start, childRoot) && isDescTreePath(path[i..], childRoot, end);
{

    if k == |path| {
        assert path[..k] == path;
        assert false;
    }else{
        TreePathNotNil(path, start, end);
        if isChild(path[k-1], path[k]) { 
            // DescPathChildrenAlt(path[(k-1)..][..2], path[k-1], end);
            assert isDescTreePath(path[(k-1)..][..2], path[k-1], path[k]);
            if |path[k-1..]| > 2 {
            AllDescPath(root, start, end, path, k, 2);

            }else{
                assert |path[k-1..]| == 2;
                assert path[(k-1)..] == path[(k-1)..][..2];
            }
        }else if isChild(path[k], path[k-1]) {
            AscTreePathAreTheSame(path[..k], start, path[k-1]);
            AscTreePathAreTheSameAlt(path[..(k+1)], start, path[k]);
            // assert isAscTreePath(path[..(k+1)], start, path[k]);
            ChildRootExists(root, start, end, path, k+1);
        }else{
            TreePathsAreTheSameAlt(path, start, end);
            assert false;
        }
    }
}


lemma AllDescPathCont(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: int,  i: int)
    requires root != Nil
    requires root !in path
    requires 1 < k < |path|
    requires 1 < i < |path[(k-1)..]|
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isAscTreePath(path[..k], start, path[k-1])
    requires isChild(path[k-1], path[k])
    requires isDescTreePath(path[(k-1)..][..i], path[k-1], path[(k-1)..][i-1])
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    ensures isDescTreePath(path[(k-1)..][..(i+1)], path[k-1], path[(k-1)..][i])
    decreases |path|-i
{
    TreePathNotNil(path, start, end);
    TreePathsAreTheSameAlt(path, start, end);
    DescPathChildren(path[(k-1)..][..i], path[k-1], path[(k-1)..][i-1]);
    if i == |path[(k-1)..]|-1 {
        if !isChild(path[(k-1)..][i-1], path[(k-1)..][i]) {
            assert isChild(path[(k-1)..][i], path[(k-1)..][i-1]);
            if i == 2 {
                assert isChild(path[(k-1)], path[(k-1)..][i-1]);
                parentsAreTheSame(path[k-1], path[k-1..][i], path[(k-1)..][i-1]);
                assert false;
            }else{
                assert isChild(path[(k-1)..][i-2], path[(k-1)..][i-1]);
                parentsAreTheSame(path[(k-1)..][i-2], path[k-1..][i], path[(k-1)..][i-1]);
                assert false;

            assert false;
            }
            assert false;
        }
        assert path[(k-1)..][..(i+1)] ==path[(k-1)..][..i] + [path[(k-1)..][i]]; 
        DescPathChildrenAlt(path[(k-1)..][..(i+1)], path[k-1], path[(k-1)..][i]);
        assert isDescTreePath(path[(k-1)..][..(i+1)], path[k-1], path[(k-1)..][i]);
    }else{
        if !isChild(path[(k-1)..][i-1], path[(k-1)..][i]) {
            assert isChild(path[(k-1)..][i], path[(k-1)..][i-1]);
            if i == 2 {
                assert isChild(path[(k-1)], path[(k-1)..][i-1]);
                parentsAreTheSame(path[k-1], path[k-1..][i], path[(k-1)..][i-1]);
                assert false;
            }else{
                assert isChild(path[(k-1)..][i-2], path[(k-1)..][i-1]);
                parentsAreTheSame(path[(k-1)..][i-2], path[k-1..][i], path[(k-1)..][i-1]);
                assert false;

            assert false;
            }
            assert false;
        }else{
            DescPathChildrenAlt(path[(k-1)..][..(i+1)], path[k-1], path[(k-1)..][i]);
            AllDescPathCont(root, start, end, path, k, i+1);
        }
    }
}

lemma AllDescPath(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: int,  i: int)
    requires root != Nil
    requires root !in path
    requires 1 < k < |path|
    requires 1 < i < |path[(k-1)..]|
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isAscTreePath(path[..k], start, path[k-1])
    requires isChild(path[k-1], path[k])
    requires isDescTreePath(path[(k-1)..][..i], path[k-1], path[(k-1)..][i-1])
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    ensures isDescTreePath(path[(k-1)..], path[k-1], path[(k-1)..][|path[(k-1)..]|-1])
    decreases |path|-i
{

    TreePathNotNil(path, start, end);
    if i == |path[(k-1)..]|-1 {
        AllDescPathCont(root, start, end, path, k, i);
        assert path[k-1..] == path[(k-1)..][..(i+1)];

    }else{
        AllDescPathCont(root, start, end, path, k, i);
        AllDescPath(root, start, end, path, k, i+1);
    }
}

lemma nonAscendingContra2(root: Tree, start: Tree, end: Tree, path: seq<Tree>, i: int)
    requires root != Nil
    requires root !in path
    requires 1 < i <= |path|
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isDescTreePath(path[..i], start, path[i-1])
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    decreases |path|-i
    ensures false 
{
    if i == |path| {
        assert path[..i] == path;

    }else{
        assert i < |path|;
        TreePathNotNil(path, start, end);
        if isChild(path[i-1], path[i]) { 
            //descending
            assert path[i] != Nil;
            assert path[..(i+1)] == path[..i]+[path[i]];
            DescPathChildren(path[..i], start, path[i-1]);
            DescPathChildrenAlt(path[..(i+1)], start, path[i]);
            assert isDescTreePath(path[..(i+1)], start, path[i]);
            nonAscendingContra2(root, start, end, path, i+1);

            assert false;
        }else if isChild(path[i], path[i-1]){
            //ascending
            DescPathChildren(path[..i], start, path[i-1]);
            assert isChild(path[i-2], path[i-1]);
            parentsAreTheSame(path[i], path[i-2], path[i-1]);
            assert false;
        }else{
            TreePathsAreTheSameAlt(path, start, end);
            assert false;
        }

    }
}


lemma rootPathAtMost3h(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    ensures |path| <= 2 * h + 1
{
    assert start in TreeSet(root);
    assert end in TreeSet(root);
    RootBounded(root, h);
    pathOptions(root, start,end, path);

    if isDescTreePath(path, start, end) {
        descRoot(root, start, end, path);
        TreeHeightToDescTreePath(root, h);
        var maxend: Tree, maxpath: seq<Tree> :| (isLeaf(maxend) && maxend in TreeSet(root)) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h+1 && isValidPath(maxpath, root) && distinct(maxpath);
        TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
        assert |path| <= |maxpath|;
    } else if isAscTreePath(path, start, end) {
        ascRoot(root, start, end, path);
        assert end == root;
        AscPathIsDescPath(path, start, root);
        ReverseIndexAll(path);
        assert |reverse(path)| == |path|;
        TreeHeightToDescTreePath(root, h);
        var maxend: Tree, maxpath: seq<Tree> :| (isLeaf(maxend) && maxend in TreeSet(root)) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h+1 && isValidPath(maxpath, root) && distinct(maxpath);
        TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
        assert |path| <= |maxpath|;
    } else if i :| 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end) {
        ReverseIndexAll(path[..(i+1)]);
        AscPathIsDescPath(path[..(i+1)],start, root);

        TreeHeightToDescTreePath(root, h);
        var maxend: Tree, maxpath: seq<Tree> :| (isLeaf(maxend) && maxend in TreeSet(root)) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h+1 && isValidPath(maxpath, root) && distinct(maxpath);
        TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
        assert |(path[..(i+1)])| <= h+1;
        assert |path[i..]| <= h+1;
        assert |path| == |reverse(path[..(i+1)])| + |path[i+1..]|;
        assert |path| <= h+1 + h;
    }
}


lemma {:vcs_split_on_every_assert} pathsWithoutRoot(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root !in path
    requires |path| > 0
    requires ChildrenAreSeparate(root)
    // requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    ensures isValidPath(path, root.left) || isValidPath(path, root.right)
{
    if root.right == Nil && root.left != Nil {
        assert isValidPath(path, root.left);
    } else if root.right != Nil && root.left == Nil {
        assert isValidPath(path, root.right);
    } else if root.right != Nil && root.left != Nil {
        if !isValidPath(path, root.left) && !isValidPath(path, root.right) {
            var badnode :| badnode in path && badnode !in TreeSet(root.left);
            var badnode2 :| badnode2 in path && badnode2 !in TreeSet(root.right);
            pathOptions2(root, start, end, path);
            if isAscTreePath(path, start, end) {
                AscPathChildrenTreeSet(path, start, end);
                if end in TreeSet(root.left) {
                    childrenInTreeSet(root.left, end, path);
                    // assert badnode2 in TreeSet(end);
                }else{
                    childrenInTreeSet(root.right, end, path);
                    // assert end in TreeSet(root.right);
                    // assert badnode in TreeSet(end);
                }
                assert false;

            }else if isDescTreePath(path, start, end) {
                DescPathChildrenTreeSet(path, start, end);
                if start in TreeSet(root.left) {
                    childrenInTreeSet(root.left, start, path);
                    // assert badnode in TreeSet(root.left);
                }else if start in TreeSet(root.right) {
                    // assert start in TreeSet(root.right);
                    childrenInTreeSet(root.right, start, path);
                    // assert badnode2 in TreeSet(root.right);
                }else {
                    assert start == root;
                }
                assert false;

            }else{
                var childRoot: Tree, i :| 0 < i < |path|-1 && path[i] == childRoot && isAscTreePath(path[..(i+1)], start, childRoot) && isDescTreePath(path[i..], childRoot, end);
                DescPathChildrenTreeSet(path[i..], childRoot, end);
                AscPathChildrenTreeSet(path[..(i+1)], start, childRoot);
                assert isValidPath(path, childRoot);
                if childRoot in TreeSet(root.left) {
                    childrenInTreeSet(root.left, childRoot, path);

                }else if childRoot in TreeSet(root.right) {
                    childrenInTreeSet(root.right, childRoot, path);
                }else{
                    assert childRoot in TreeSet(root);
                    assert childRoot == root;
                }

                assert false;
            }
            assert false;
        }
    }
}

lemma childHeightIsLessThanPath(root: Tree, child:Tree, h: int, end: Tree)
    requires root != Nil
    requires ChildrenAreSeparate(root)
    requires h == TreeHeight(root)
    requires isChild(root, child)
    requires TreeHeight(child) <= h-1
    ensures forall rootedPath: seq<Tree>, anyend: Tree :: isDescTreePath(rootedPath, child, anyend)  && isValidPath(rootedPath, child) && distinct(rootedPath) ==> |rootedPath| <= h
{
    forall rootedPath: seq<Tree>, anyend: Tree | isDescTreePath(rootedPath, child, anyend)  && isValidPath(rootedPath, child) && distinct(rootedPath)
        ensures |rootedPath| <= h
    {
        if |rootedPath| <= h {

        }else if |rootedPath| > h {
            TreeHeightMax(child);
            EndDeterminesPath(rootedPath, child, anyend);
            if anyend in TreeSet(child.left) {
                if child.left == Nil {
                    assert false;
                }else{
                    childHeightIsLessThanPath(child, child.left, TreeHeight(child), anyend);
                    assert forall childPaths: seq<Tree>, anyend: Tree ::  isDescTreePath(childPaths, child.left, anyend)  && isValidPath(childPaths, child.left) && distinct(childPaths) ==> |childPaths| <= TreeHeight(child);
                    assert rootedPath[1] == child.left;
                    assert rootedPath == [child] + rootedPath[1..];
                    isDescPathAndValidImpliesAllValid(rootedPath,child,anyend);
                    assert isDescTreePath(rootedPath[1..], child.left, anyend);
                    // assert isValidPath(rootedPath[1..], child.left);
                    // assert |rootedPath[1..]| <= TreeHeight(child);
                    assert false;
                }

            }else if anyend in TreeSet(child.right) {
                if child.right == Nil {
                    assert false;
                }else{

                    childHeightIsLessThanPath(child, child.right, TreeHeight(child), anyend);
                    // assert forall childPaths: seq<Tree>, anyend: Tree ::  isDescTreePath(childPaths, child.right, anyend)  && isValidPath(childPaths, child.right) && distinct(childPaths) ==> |childPaths| <= TreeHeight(child);
                    isDescPathAndValidImpliesAllValid(rootedPath,child,anyend);
                    assert isDescTreePath(rootedPath[1..], child.right, anyend);
                    assert false;
                }
            }else{
                assert anyend !in TreeSet(child.right) && anyend !in TreeSet(child.left);
                if anyend == child {

                }else{
                    assert anyend !in TreeSet(child);
                    assert false;
                }
            }

        }
    }
}

lemma TreeHeightToMaxDescTreePath(root: Tree, h: int, end: Tree, path: seq<Tree>) 
    requires root != Nil
    requires ChildrenAreSeparate(root)
    requires h == TreeHeight(root)
    requires end != Nil  && end in TreeSet(root)
    requires isDescTreePath(path, root, end)
    requires |path| == h+1
    requires isValidPath(path, root) 
    requires distinct(path)
    ensures forall rootedPath: seq<Tree>, anyend: Tree :: isDescTreePath(rootedPath, root, anyend)  && isValidPath(rootedPath, root) && distinct(rootedPath) ==> |rootedPath| <= |path|
    
{
    TreeHeightMax(root);
    RootBounded(root, h);
    forall rootedPath: seq<Tree>, anyend: Tree | isDescTreePath(rootedPath, root, anyend)  && isValidPath(rootedPath, root) && distinct(rootedPath)
        ensures |rootedPath| <= |path|
    {
        assert rootedPath[0] == root;
        assert |rootedPath| >= 1;
        if |rootedPath| == 1 {

        }else{
            EndDeterminesPath(rootedPath, root, anyend);
            if anyend in TreeSet(root.left) {
                childHeightIsLessThanPath(root, root.left, h, anyend);
                // assert forall childPaths: seq<Tree>, anyend: Tree ::  isDescTreePath(childPaths, root.left, anyend)  && isValidPath(childPaths, root.left) && distinct(childPaths) ==> |childPaths| <= h;
                isDescPathAndValidImpliesAllValid(rootedPath,root,anyend);
                assert isDescTreePath(rootedPath[1..], root.left, anyend);
                assert |rootedPath[1..]| <= h;
                assert |rootedPath| <= h+1;
            }else if anyend in TreeSet(root.right) {
                childHeightIsLessThanPath(root, root.right, h, anyend);
                isDescPathAndValidImpliesAllValid(rootedPath,root,anyend);
                assert isDescTreePath(rootedPath[1..], root.right, anyend);
                assert |rootedPath[1..]| <= h;
                assert |rootedPath| <= h+1;
            }else{
                if anyend == root {

                }else{
                    assert anyend !in TreeSet(root);
                    assert false;
                }
            }
        }
    }
   
}

lemma {:induction false} rootPathMaxLeft(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    requires root.left != Nil
    requires root.right == Nil
    requires |path| == 1+TreeHeight(root)
    ensures largestRootedPath(path, root)
{
    TreePathNotNil(path, start, end);
    forall astart: Tree, aend: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, astart, aend) && isValidPath(paths, root)
        ensures 1+TreeHeight(root) >= |paths|
    {
        pathOptions(root, start, end, path);
        if isAscTreePath(path, start, end) {
            ascRoot(root, start, end, path);
            ReverseIndexAll(path);
            AscPathIsDescPath(path, start, root);
            TreeHeightToMaxDescTreePath(root, h, start, reverse(path));
            pathOptions(root, astart, aend, paths);
            if isAscTreePath(paths, astart, aend) {
                ascRoot(root, astart, aend, paths);
                ReverseIndexAll(paths);
                AscPathIsDescPath(paths, astart, root);

                assert 1+TreeHeight(root) >= |paths|;
            }else if isDescTreePath(paths, astart, aend) {
                descRoot(root, astart, aend, paths);

                assert 1+TreeHeight(root) >= |paths|;
            }else{
                var i :| 0 < i < |paths|-1 && paths[i] == root && isAscTreePath(paths[..(i+1)], astart, root) && isDescTreePath(paths[i..], root, aend);
                assert paths[i-1] == paths[i+1] by {
                    AscPathChildren(paths[..(i+1)], astart, root);
                    assert isChild(paths[i], paths[i-1]);
                    assert isChild(paths[i], paths[i+1]);
                    TreePathNotNil(paths, astart, aend);
                    assert paths[i-1] != Nil;
                    assert paths[i+1] != Nil;
                }
                assert false;
            }

            assert 1+TreeHeight(root) >= |paths|;
        } else if isDescTreePath(path, start, end) {
            descRoot(root, start, end, path);
            TreeHeightToMaxDescTreePath(root, h, end, path);
            pathOptions(root, astart, aend, paths);
            if isAscTreePath(paths, astart, aend) {
                ascRoot(root, astart, aend, paths);
                ReverseIndexAll(paths);
                AscPathIsDescPath(paths, astart, root);

                assert 1+TreeHeight(root) >= |paths|;
            }else if isDescTreePath(paths, astart, aend) {
                descRoot(root, astart, aend, paths);

                assert 1+TreeHeight(root) >= |paths|;
            }else{
                var i :| 0 < i < |paths|-1 && paths[i] == root && isAscTreePath(paths[..(i+1)], astart, root) && isDescTreePath(paths[i..], root, aend);
                assert paths[i-1] == paths[i+1] by {
                    TreePathNotNil(paths, astart, aend);
                    assert paths[i-1] != Nil;
                    assert paths[i+1] != Nil;
                    assert isChild(paths[i], paths[i-1]) by {
                        AscPathChildren(paths[..(i+1)], astart, root);
                        assert i-1 < |paths[..(i+1)]|-1;

                    }
                    assert isChild(paths[i], paths[i+1]);
                }
                assert false;
            }
            assert 1+TreeHeight(root) >= |paths|;
        }else{
            var i :| 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
            assert isChild(path[i], path[i-1]) by {
                AscPathChildren(path[..(i+1)], start, root);

            }
            assert isChild(path[i], path[i+1]);
            assert false;
        }
    }
}

lemma {:induction false}  rootPathMaxRight(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    requires root.left == Nil
    requires root.right != Nil
    requires |path| == 1+TreeHeight(root)
    ensures largestRootedPath(path, root)
{
    TreePathNotNil(path, start, end);
    forall astart: Tree, aend: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, astart, aend) && isValidPath(paths, root)
        ensures 1+TreeHeight(root) >= |paths|
    {
        pathOptions(root, start, end, path);
        if isAscTreePath(path, start, end) {
            ascRoot(root, start, end, path);
            ReverseIndexAll(path);
            AscPathIsDescPath(path, start, root);
            TreeHeightToMaxDescTreePath(root, h, start, reverse(path));
            pathOptions(root, astart, aend, paths);
            if isAscTreePath(paths, astart, aend) {
                ascRoot(root, astart, aend, paths);
                ReverseIndexAll(paths);
                AscPathIsDescPath(paths, astart, root);

                assert 1+TreeHeight(root) >= |paths|;
            }else if isDescTreePath(paths, astart, aend) {
                descRoot(root, astart, aend, paths);

                assert 1+TreeHeight(root) >= |paths|;
            }else{
                var i :| 0 < i < |paths|-1 && paths[i] == root && isAscTreePath(paths[..(i+1)], astart, root) && isDescTreePath(paths[i..], root, aend);
                assert paths[i-1] == paths[i+1] by {
                    TreePathNotNil(paths, astart, aend);
                    assert paths[i-1] != Nil;
                    assert paths[i+1] != Nil;
                    assert isChild(paths[i], paths[i-1]) by {
                        AscPathChildren(paths[..(i+1)], astart, root);
                    }
                    assert isChild(paths[i], paths[i+1]);
                }
                assert false;
            }

            assert 1+TreeHeight(root) >= |paths|;
        } else if isDescTreePath(path, start, end) {
            descRoot(root, start, end, path);
            TreeHeightToMaxDescTreePath(root, h, end, path);
            pathOptions(root, astart, aend, paths);
            if isAscTreePath(paths, astart, aend) {
                ascRoot(root, astart, aend, paths);
                ReverseIndexAll(paths);
                AscPathIsDescPath(paths, astart, root);

                // assert 1+TreeHeight(root) >= |paths|;
            }else if isDescTreePath(paths, astart, aend) {
                descRoot(root, astart, aend, paths);

                // assert 1+TreeHeight(root) >= |paths|;
            }else{
                var i :| 0 < i < |paths|-1 && paths[i] == root && isAscTreePath(paths[..(i+1)], astart, root) && isDescTreePath(paths[i..], root, aend);
                assert paths[i-1] == paths[i+1] by {
                    TreePathNotNil(paths, astart, aend);
                    assert paths[i-1] != Nil;
                    assert paths[i+1] != Nil;
                    AscPathChildren(paths[..(i+1)], astart, root);
                    assert isChild(paths[i], paths[i-1]);
                    assert isChild(paths[i], paths[i+1]);
                }
                assert false;
            }
            assert 1+TreeHeight(root) >= |paths|;
        }else{
            var i :| 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
            assert path[i] == path[i+1] by {
            AscPathChildren(path[..(i+1)], start, root);
            assert isChild(path[i], path[i-1]);
            assert isChild(path[i], path[i+1]);

            }
            assert false;
        }
    }
}

lemma {:induction false} {:vcs_split_on_every_assert}  rootPathMax(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    requires root.left == Nil && root.right == Nil ==> |path| == 1
    requires root.left != Nil && root.right == Nil ==> |path| == 1+TreeHeight(root)
    requires root.left == Nil && root.right != Nil ==> |path| == 1+TreeHeight(root)
    requires root.left != Nil && root.right != Nil ==> |path| == 3+TreeHeight(root.right)+TreeHeight(root.left)
    ensures largestRootedPath(path, root)
{
    TreePathNotNil(path, start, end);
    if root.left == Nil && root.right == Nil {
        forall start: Tree, end: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
            ensures |[root]| >= |paths|
        {
           if |paths| > 1 {
            if paths[0] != root {
                    assert paths[0] !in TreeSet(root);

            }else{
                if paths[1] != root{
                    assert paths[1] !in TreeSet(root);
                }else{
                    assert paths[0] == paths[1];

                }
            }

            assert false;
           } 
        }
        assert largestRootedPath([root], root);
    }

    if root.left != Nil && root.right == Nil {
        rootPathMaxLeft(root, start, end, path, h);
    }

    if root.left == Nil && root.right != Nil {
        rootPathMaxRight(root,start, end, path, h);
    }

    if root.left != Nil && root.right != Nil {
        forall astart: Tree, aend: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, astart, aend) && isValidPath(paths, root)
            ensures 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|
        {
            pathOptions(root, start, end, path);
            if isAscTreePath(path, start, end) {
                ascRoot(root, start, end, path);
                ReverseIndexAll(path);
                AscPathIsDescPath(path, start, root);
                TreeHeightToDescTreePath(root, h);
                var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root))  && isDescTreePath(dpath, root, dend) && |dpath| == h+1 && isValidPath(dpath, root) && distinct(dpath);
                TreeHeightToMaxDescTreePath(root, h, dend, dpath);
                assert false;

            } else if isDescTreePath(path, start, end) {
                descRoot(root, start, end, path);
                TreeHeightToDescTreePath(root, h);
                var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root))  && isDescTreePath(dpath, root, dend) && |dpath| == h+1 && isValidPath(dpath, root) && distinct(dpath);
                TreeHeightToMaxDescTreePath(root, h, dend, dpath);
                assert false;

            }else{
                var i :| 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
                pathOptions(root, astart, aend, paths);
                if isAscTreePath(paths, astart, aend) {
                    TreeHeightToDescTreePath(root, h);
                    var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root))  && isDescTreePath(dpath, root, dend) && |dpath| == h+1 && isValidPath(dpath, root) && distinct(dpath);
                    TreeHeightToMaxDescTreePath(root, h, dend, dpath);
                    ascRoot(root, astart, aend, paths);
                    ReverseIndexAll(paths);
                    AscPathIsDescPath(paths, astart, root);
                    assert isDescTreePath(reverse(paths), root, astart);
                    assert |paths| <= |dpath|;
                    assert 3+TreeHeight(root.right)+TreeHeight(root.left) > |dpath|;

                } else if isDescTreePath(paths, astart, aend) {
                    descRoot(root, astart, aend, paths);
                    TreeHeightToDescTreePath(root, h);
                    var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root))  && isDescTreePath(dpath, root, dend) && |dpath| == h+1 && isValidPath(dpath, root) && distinct(dpath);
                    TreeHeightToMaxDescTreePath(root, h, dend, dpath);
                    assert isDescTreePath(paths, root, aend);
                    assert |paths| <= |dpath|;
                    assert 3+TreeHeight(root.right)+TreeHeight(root.left) > |dpath|;

                    assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
                }else{
                    var j :| 0 < j < |paths|-1 && paths[j] == root && isAscTreePath(paths[..(j+1)], astart, root) && isDescTreePath(paths[j..], root, aend);
                    TreePathNotNil(paths, astart, aend);
                    rootPathAtMost3h(root, astart, aend, paths, h);
                    DescTreePathToPath(paths[(j+1)..], paths[j+1], aend);
                    AscTreePathSplit(paths[..(j+1)], astart, root);
                    assert paths[..(j+1)][..|paths[..(j+1)]|-1] == paths[..j];
                    assert isAscTreePath(paths[..j], astart, paths[j-1]) by {
                    }
                    AscTreePathToPath(paths[..j], astart, paths[j-1]);
                    pathsWithoutRoot(root, astart, paths[j-1], paths[..j], h);
                    pathsWithoutRoot(root, paths[j+1], aend, paths[(j+1)..], h);
                    if isValidPath(paths[(j+1)..], root.left) && isValidPath(paths[..j], root.left) {
                        assert paths[j-1] == paths[j+1] by {
                            AscPathChildren(paths[..(j+1)], astart, paths[j]);
                            assert isChild(paths[j], paths[j-1]);
                            assert isChild(paths[j], paths[j+1]);
                        }
                        assert false;
                    } else if isValidPath(paths[(j+1)..], root.right) && isValidPath(paths[..j], root.right) {
                        assert paths[j-1] == paths[j+1] by {
                            AscPathChildren(paths[..(j+1)], astart, paths[j]);
                            assert isChild(paths[j], paths[j-1]);
                            assert isChild(paths[j], paths[j+1]);
                        }
                        assert false;
                    } else if isValidPath(paths[(j+1)..], root.left) && isValidPath(paths[..j], root.right) {
                        assert TreeHeight(root.left) <= h-1;
                        assert TreeHeight(root.right) <= h-1;

                        TreeHeightToDescTreePath(root.left, TreeHeight(root.left));
                        var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root.left))  && isDescTreePath(dpath, root.left, dend) && |dpath| == TreeHeight(root.left)+1 && isValidPath(dpath, root.left) && distinct(dpath);
                        TreeHeightToMaxDescTreePath(root.left, TreeHeight(root.left), dend, dpath);
                        assert isDescTreePath(paths[j+1..], root.left, aend);
                        assert |paths[j+1..]| <= TreeHeight(root.left)+1;


                        TreeHeightToDescTreePath(root.right, TreeHeight(root.right));
                        var rend: Tree, rpath: seq<Tree> :| (isLeaf(rend) && rend in TreeSet(root.right))  && isDescTreePath(rpath, root.right, rend) && |rpath| == TreeHeight(root.right)+1 && isValidPath(rpath, root.right) && distinct(rpath);
                        TreeHeightToMaxDescTreePath(root.right, TreeHeight(root.right), rend, rpath);

                        ReverseIndexAll(paths[..j]);
                        assert paths[j-1] == root.right by {
                            AscPathChildren(paths[..(j+1)], astart, paths[j]);
                            assert isChild(root, paths[j-1]);
                        }
                        AscPathIsDescPath(paths[..j], astart, root.right);
                        assert isDescTreePath(reverse(paths[..j]), root.right, astart);
                        assert |paths[..j]| <= TreeHeight(root.right)+1;
                        assert paths == paths[..j]+[root]+paths[j+1..];
                        assert |paths| <= TreeHeight(root.right)+1 + 1 + TreeHeight(root.left)+1;

                        assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
                    } else if isValidPath(paths[(j+1)..], root.right) && isValidPath(paths[..j], root.left) {
                        assert TreeHeight(root.left) <= h-1;
                        assert TreeHeight(root.right) <= h-1;

                        TreeHeightToDescTreePath(root.right, TreeHeight(root.right));
                        var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root.right))  && isDescTreePath(dpath, root.right, dend) && |dpath| == TreeHeight(root.right)+1 && isValidPath(dpath, root.right) && distinct(dpath);
                        TreeHeightToMaxDescTreePath(root.right, TreeHeight(root.right), dend, dpath);
                        assert isDescTreePath(paths[j+1..], root.right, aend);
                        assert |paths[j+1..]| <= TreeHeight(root.right)+1;


                        TreeHeightToDescTreePath(root.left, TreeHeight(root.left));
                        var rend: Tree, rpath: seq<Tree> :| (isLeaf(rend) && rend in TreeSet(root.left))  && isDescTreePath(rpath, root.left, rend) && |rpath| == TreeHeight(root.left)+1 && isValidPath(rpath, root.left) && distinct(rpath);
                        TreeHeightToMaxDescTreePath(root.left, TreeHeight(root.left), rend, rpath);

                        ReverseIndexAll(paths[..j]);
                        assert paths[j-1] == root.left by {
                            AscPathChildren(paths[..(j+1)], astart, paths[j]);
                            assert isChild(root, paths[j-1]);
                        }
                        AscPathIsDescPath(paths[..j],  astart, root.left);
                        assert isDescTreePath(reverse(paths[..j]), root.left, astart);
                        assert |paths[..j]| <= TreeHeight(root.left)+1;
                        assert paths == paths[..j]+[root]+paths[j+1..];
                        assert |paths| <= TreeHeight(root.right)+1 + 1 + TreeHeight(root.left)+1;

                        assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
                    }else{
                        assert false;
                    }
                    assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
                }

            }
             assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
        }
    }
}

lemma BothCases(root: Tree, left: Tree, right: Tree, h1: int, h2: int)
    requires root != Nil && left != Nil && right != Nil
    requires ChildrenAreSeparate(root)
    requires root.left == left && root.right == right
    requires TreeHeight(root.left) == h1
    requires TreeHeight(root.right) == h2
    ensures exists start: Tree, end: Tree, path: seq<Tree> :: root in path && isTreePath(path, start, end) && |path| == h1+h2 + 3 && isValidPath(path, root) && distinct(path);
{

        TreeHeightToDescTreePath(right, h2);
        var rpath: seq<Tree>, rend: Tree :| (isLeaf(rend) && rend in TreeSet(right))  && isDescTreePath(rpath, right, rend) && |rpath| == h2+1 && isValidPath(rpath, right) && distinct(rpath);
        // assert rend in TreeSet(right);
        assert isDescTreePath([root]+rpath, root, rend);
        DescTreePathToPath(rpath, root.right, rend);
        TreeHeightToDescTreePath(left, h1);
        var lpath: seq<Tree>, lend: Tree :| (isLeaf(lend) && lend in TreeSet(left))  && isDescTreePath(lpath, left, lend) && |lpath| == h1+1 && isValidPath(lpath, left) && distinct(lpath);
        // assert isDescTreePath([root]+lpath, root, lend);
        DescTreePathToPath(lpath, root.left, lend);
        
        parentNotInTreeSet(root, left);
        parentNotInTreeSet(root, right);
        // assert root !in TreeSet(left);
        // assert root !in TreeSet(right);
        // assert lend in TreeSet(left);
        distincts([root], lpath);
        // assert distinct([root]+lpath);
        reverseDistinct([root]+lpath);
        assert rend != lend;
        DescPlusDesc([root]+rpath, lend, root, [root]+lpath, rend);
        // assert isTreePath(reverse([root]+lpath)+rpath, lend, rend);
        assert |[root]+lpath| == h1+2;
        ReverseIndexAll([root]+lpath);
        // assert |[root]+lpath| == h1+2;
        // assert |reverse([root]+lpath)+rpath| == h1+h2+3;
        distincts(reverse([root]+lpath), rpath);
}

ghost predicate largestPath(path: seq<Tree>, root: Tree) {
    forall start: Tree, end: Tree, paths: seq<Tree> :: distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) ==> |path| >= |paths|
}

ghost function allPaths(root: Tree): iset<seq<Tree>> {
    iset start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) :: paths
}

ghost function allRootedPaths(root: Tree): iset<seq<Tree>> {
    iset start: Tree, end: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) :: paths
}

lemma pathSums(root: Tree)
    requires root != Nil
    requires ChildrenAreSeparate(root)
    ensures allPaths(root) == allRootedPaths(root)+allPaths(root.left)+allPaths(root.right)
{
    forall path | path in allPaths(root)
        ensures path in allRootedPaths(root)+allPaths(root.left)+allPaths(root.right)
    {
        if root in path {
            assert path in allRootedPaths(root);
        }else{
            pathsWithoutRoot(root, path[0], path[|path|-1], path, TreeHeight(root));
        }
    }

    forall path | path in allRootedPaths(root)+allPaths(root.left)+allPaths(root.right)
        ensures path in allPaths(root)
    {
        
    }
}

ghost predicate largestRootedPath(path: seq<Tree>, root: Tree) {
    root in path && isPath(path, path[0], path[|path|-1], root) && forall start: Tree, end: Tree, paths: seq<Tree> :: root in paths && distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) ==> |path| >= |paths|
}

lemma NullLargest(path: seq<Tree>, root: Tree) 
    requires root == Nil
    requires path == []
    ensures largestPath(path, root)
{
    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) 
        ensures |path| >= |paths|
    {
        if |paths| > 0 {
            assert paths[0] != Nil;
            assert TreeSet(root) == {};
            assert paths[0] in TreeSet(root);
            assert false;
        }

    }
}

lemma lpR(root: Tree)
    requires root != Nil && root.left == Nil && root.right == Nil
    ensures largestPath([root], root)
{
    assert distinct([root]);
    assert isValidPath([root], root);
    assert isTreePath([root], root, root);

    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
     ensures |[root]| >= |paths|
    {
        if |paths| > 1 {
            assert paths[0] != paths[1];
            if isChild(paths[0], paths[1]) {
                if paths[0] == root {
                    assert false;
                }else if paths[1] == root {
                    parentNotInTreeSet(paths[0], root);
                    assert false;
                }else{
                    assert paths[0] !in TreeSet(root);
                }
            } else if isChild(paths[1], paths[0]) {
                if paths[0] == root {
                    parentNotInTreeSet(paths[1], root);
                    assert false;
                }else if paths[1] == root {
                    parentNotInTreeSet(paths[0], root);
                    assert false;
                }
            }else {
                assert false;
            }
        }else if |paths| == 0{

        }else{

        }
    }

}


// // https://www.youtube.com/watch?v=2PFl93WM_ao
// //Property I 
// //Deepest branch contain the maximal diameter

// //Suppose c1 does not contain the diameter.
// //d_1 = D(c1)
// //d_2 = =D(c_i)
// //d1+d2+2 >= d2
// //d1 = d2 + delta where delta >=0
// //d1 + d2 +2 == d2+delta +d2+2 == 2*d2+delta+2 > 2*d2
// //How many diameters can be in a tree with n nodes?
// //Count the number of diametes in T?

lemma LargestRootBoth(root: Tree, h: int, 
leftPath: seq<Tree>, rightPath: seq<Tree>, 
leftWidth: int, rightWidth: int, 
diameter: int, rootPath: seq<Tree>, rootDim: int, greatestPath: seq<Tree>, start: Tree, end: Tree)
    requires ChildrenAreSeparate(root)
    requires root != Nil
    requires h == TreeHeight(root)
    requires largestPath(leftPath, root.left)
    requires largestPath(rightPath, root.right)
    requires largestRootedPath(rootPath, root)

    requires distinct(rootPath)
    requires root in rootPath
    requires rootDim == |rootPath|-1
    requires |rootPath| == 3+TreeHeight(root.right)+TreeHeight(root.left) 
    requires leftWidth == |leftPath| - 1
    requires rightWidth == |rightPath| - 1
    requires root.left != Nil && root.right != Nil
    requires diameter == max(leftWidth, max(rightWidth, TreeHeight(root.left)+TreeHeight(root.right)+2))
    requires |greatestPath|-1 == diameter
    requires isTreePath(greatestPath, start,end)
    requires isValidPath(greatestPath, root)
    requires distinct(greatestPath)
    ensures largestPath(greatestPath, root)
{
    pathSums(root);
    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
        ensures |greatestPath| >= |paths|
    {
        if diameter == leftWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        } else if diameter == rightWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;

        } else if diameter == TreeHeight(root.left)+TreeHeight(root.right)+2 {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        }
    }
}

lemma LargestRootLeft(root: Tree, h: int, 
leftPath: seq<Tree>, rightPath: seq<Tree>, 
leftWidth: int, rightWidth: int, 
diameter: int, rootPath: seq<Tree>, rootDim: int, greatestPath: seq<Tree>, start: Tree, end: Tree)
    requires ChildrenAreSeparate(root)
    requires root != Nil
    requires h == TreeHeight(root)
    requires largestPath(leftPath, root.left)
    requires largestPath(rightPath, root.right)
    requires largestRootedPath(rootPath, root)

    requires distinct(rootPath)
    requires root in rootPath
    requires rootDim == |rootPath|-1
    requires |rootPath| == 1+TreeHeight(root) 
    requires leftWidth == |leftPath| - 1
    requires rightWidth == |rightPath| - 1
    requires root.left != Nil && root.right == Nil
    requires diameter == max(leftWidth, max(rightWidth, TreeHeight(root.left)+TreeHeight(root.right)+2))
    requires |greatestPath|-1 == diameter
    requires isTreePath(greatestPath, start,end)
    requires isValidPath(greatestPath, root)
    requires distinct(greatestPath)
    ensures largestPath(greatestPath, root)
{
    pathSums(root);
    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
        ensures |greatestPath| >= |paths|
    {
        if diameter == leftWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        } else if diameter == rightWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;

        } else if diameter == TreeHeight(root.left)+TreeHeight(root.right)+2 {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        }
    }
}

lemma LargestRootRight(root: Tree, h: int, 
leftPath: seq<Tree>, rightPath: seq<Tree>, 
leftWidth: int, rightWidth: int, 
diameter: int, rootPath: seq<Tree>, rootDim: int, greatestPath: seq<Tree>, start: Tree, end: Tree)
    requires ChildrenAreSeparate(root)
    requires root != Nil
    requires h == TreeHeight(root)
    requires largestPath(leftPath, root.left)
    requires largestPath(rightPath, root.right)
    requires largestRootedPath(rootPath, root)

    // requires distinct(rootPath)
    // requires root in rootPath
    requires rootDim == |rootPath|-1
    requires |rootPath| == 1+TreeHeight(root) 
    requires leftWidth == |leftPath| - 1
    requires rightWidth == |rightPath| - 1
    requires root.left == Nil && root.right != Nil
    requires diameter == max(leftWidth, max(rightWidth, TreeHeight(root.left)+TreeHeight(root.right)+2))
    requires |greatestPath|-1 == diameter
    requires isTreePath(greatestPath, start,end)
    requires isValidPath(greatestPath, root)
    requires distinct(greatestPath)
    ensures largestPath(greatestPath, root)
{
    pathSums(root);
    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
        ensures |greatestPath| >= |paths|
    {
        if diameter == leftWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        } else if diameter == rightWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;

        } else if diameter == TreeHeight(root.left)+TreeHeight(root.right)+2 {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        }
    }
}


method diameter(root: Tree) returns (heightDim: (int, int))
    requires ChildrenAreSeparate(root)
    ensures root == Nil ==> heightDim == (-1, -1)
    ensures root != Nil && root.left == Nil && root.right == Nil ==> heightDim == (0, 0)
    ensures heightDim.0 == TreeHeight(root)
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == heightDim.1  && isValidPath(path, root) && distinct(path) && largestPath(path, root)
{
    if root == Nil {
        return (-1, -1);
    }
    if root.left == Nil && root.right == Nil {
        ghost var path := [root];
        assert isTreePath([root], root, root);
        lpR(root);
        return (0,0);
    }
    var leftDiameter := diameter(root.left);
    var rightDiameter := diameter(root.right);
    var height := max(leftDiameter.0, rightDiameter.0) + 1;
    var dim := leftDiameter.0 + rightDiameter.0 + 2;
    var maxDiameter := max(leftDiameter.1, max(rightDiameter.1, dim));

    if root.right != Nil && root.left != Nil {
        BothCases(root, root.left, root.right, leftDiameter.0, rightDiameter.0);
        ghost var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1 && isValidPath(rightPath, root) && distinct(rightPath) && largestPath(rightPath, root.right);
        ghost var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1 && isValidPath(leftPath, root) && distinct(leftPath) && largestPath(leftPath, root.left);
        ghost var start, end, path :| root in path && isTreePath(path, start, end) && |path| == leftDiameter.0 + rightDiameter.0 + 3 && isValidPath(path, root) && distinct(path);
        rootPathMax(root, start, end, path, TreeHeight(root));
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert maxDiameter == leftDiameter.1;
            LargestRootBoth(root, TreeHeight(root), leftPath, rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, path, dim, leftPath, lstart, lend);
        }else if rightDiameter.1 > dim {
            LargestRootBoth(root, TreeHeight(root), leftPath, rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, path, dim, rightPath, rstart, rend);
            assert maxDiameter == rightDiameter.1;
        }else{
            assert |path| >= |rightPath|;
            assert |path| >= |leftPath|;
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            assert |path| - 1 == dim;
            assert maxDiameter == dim;
            LargestRootBoth(root, TreeHeight(root), leftPath, rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, path, dim, path, start, end);
        }
    } else if root.right != Nil {
        ghost var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1 && isValidPath(rightPath, root) && distinct(rightPath) && largestPath(rightPath, root.right);
        TreeHeightToDescTreePath(root.right, rightDiameter.0);
        ghost var rpath: seq<Tree>, end: Tree :| (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.right))  && isDescTreePath(rpath, root.right, end) && |rpath| == rightDiameter.0+1 && isValidPath(rpath, root.right) && distinct(rpath);
        assert isDescTreePath([root]+rpath, root, end);
        DescTreePathToPath([root]+rpath, root, end);
        assert |[root]+rpath| == rightDiameter.0+2;
        parentNotInTreeSet(root, root.right);
        assert distinct([root]+rpath);
        assert leftDiameter.0 == -1;
        assert leftDiameter.1 == -1;
        NullLargest([], root.left);
        rootPathMax(root, root, end, [root]+rpath, TreeHeight(root));
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert false;
        }else if rightDiameter.1 > dim {
            assert maxDiameter == rightDiameter.1;
            // assert TreeHeight(root.right)+1 == TreeHeight(root);
            // assert |rpath| == TreeHeight(root.right)+1;
            // assert |[root]+rpath| == TreeHeight(root.right)+2;
         
            LargestRootRight(root, TreeHeight(root), [], rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, [root]+rpath, dim, rightPath, rstart, rend);
        }else{
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            calc {
                dim;
                leftDiameter.0 + rightDiameter.0 + 2;
                -1 + rightDiameter.0 + 2;
                rightDiameter.0 + 1;
            }
            assert maxDiameter == dim;
            assert |[root]+rpath| - 1 == dim;
            rootPathMax(root, root, end, [root]+rpath, TreeHeight(root));
            LargestRootRight(root, TreeHeight(root), [], rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, [root]+rpath, dim, [root]+rpath, root, end);
        }
    } else if root.left != Nil {
        ghost var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1 && isValidPath(leftPath, root.left) && distinct(leftPath) && largestPath(leftPath, root.left);
        TreeHeightToDescTreePath(root.left, leftDiameter.0);
        ghost var lpath: seq<Tree>, end: Tree :| (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.left))  && isDescTreePath(lpath, root.left, end) && |lpath| == leftDiameter.0+1 && isValidPath(lpath, root.left) && distinct(lpath);
        assert isDescTreePath([root]+lpath, root, end);
        DescTreePathToPath([root]+lpath, root, end);
        parentNotInTreeSet(root, root.left);
        assert distinct([root]+lpath);
        assert dim == leftDiameter.0 + 1;
        assert rightDiameter.0 == -1;
        assert rightDiameter.1 == -1;
        assert leftDiameter.1 >= 0;
        NullLargest([], root.right);
        rootPathMax(root, root, end, [root]+lpath, TreeHeight(root));
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert maxDiameter == leftDiameter.1;
            LargestRootLeft(root, TreeHeight(root), leftPath, [], leftDiameter.1, rightDiameter.1, maxDiameter, [root]+lpath, dim, leftPath, lstart, lend);
        }else if rightDiameter.1 > dim {
            assert false;
        }else{
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            assert maxDiameter == dim;
            LargestRootLeft(root, TreeHeight(root), leftPath, [], leftDiameter.1, rightDiameter.1, maxDiameter, [root]+lpath, dim, [root]+lpath, root, end);
        }

    }

    return (height, maxDiameter);
}

method diameterOfBinaryTree(root: Tree) returns (maxDiameter: int)
    requires ChildrenAreSeparate(root)
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == maxDiameter && isValidPath(path, root) && distinct(path)
{
    var result := diameter(root);
    maxDiameter := result.1;
}
}
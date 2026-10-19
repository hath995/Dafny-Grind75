/*
//Given an integer array nums, return true if any value appears at least twice in the array, and return false if every element is distinct.

 https://leetcode.com/problems/contains-duplicate/

function containsDuplicate(nums: number[]): boolean {
    let m = new Set();
    for(let elem of nums) {
        if(m.has(elem)) {
            return true;
        }
        m.add(elem);
    }
    return false;
};
*/
function seqSet(nums: seq<int>, index: nat): set<int> {
    set x | 0 <= x < index < |nums| :: nums[x]
}

predicate hasDuplicate(s : seq<int>)
{
	exists i,j :: 0 <= i < j < |s| && s[i] == s[j]
}

lemma AppendingUniqueElement(s : seq<int>, a : int)
	requires !hasDuplicate(s)
	requires forall j :: 0 <= j < |s| ==> a != s[j]
	ensures !hasDuplicate(s + [a])
{
	
}

method containsDuplicateI(s : seq<int>)
		returns (b : bool)
	ensures hasDuplicate(s) ==> b
	ensures b ==> hasDuplicate(s)
{
	b := false;
	var i := 0;
	var elems: set<int> := {};

	while i != |s|
		invariant 0 <= i <= |s|
		invariant forall j :: 0 <= j < i ==> s[j] in elems
		invariant forall el :: el in elems ==> (exists h :: 0 <= h < i && s[h] == el)
		invariant !hasDuplicate(s[0..i])
	{
		if s[i] in elems {
			b := true;
			assert hasDuplicate(s[0..i+1]);
			break;
		}
		assert !(s[i] in elems);
		ghost var elems' := elems;
		elems := elems + {s[i]};
		ghost var i' := i;
		i := i + 1;
		
		assert !hasDuplicate(s[0..i']);
		assert forall j :: 0 <= j < i' ==> s[j] != s[i'];
		assert !hasDuplicate(s[0..i]);
	}
}

/*
https://leetcode.com/problems/contains-duplicate-ii/
Given an integer array nums and an integer k, return true if there are two distinct indices i and j in the array such that nums[i] == nums[j] and abs(i - j) <= k.

function containsNearbyDuplicate(nums: number[], k: number): boolean {
    let windowSet = new Set();
    const n = nums.length;
    if(k == 0) return false;
    for(let i = 0; i < n; i++) {
        if(windowSet.has(nums[i])) {
            return true;
        }
        if(i >= k) {
            windowSet.delete(nums[i-k]);
        }
        windowSet.add(nums[i]);
    }
    return false;
};

*/

method containsNearbyDuplicate(nums: seq<int>, k: nat) returns (containsDuplicate: bool) 
    requires k <= |nums|
    requires |nums| < 10
    ensures containsDuplicate ==> exists i,j :: 0 <= i < j < |nums| && j-i <= k && nums[i] == nums[j]
{
    var windowSet: set<int> := {};
    if k == 0 {
        return false;
    }

    for i: nat := 0 to |nums| 
        invariant 1 <= k <= |nums|
        invariant windowSetValid(nums, k, i, windowSet)
    {
        if nums[i] in windowSet {
            windowSetValidIsSufficient(nums, k, i, windowSet);
            return true;
        }
        windowSet := if i >= k then (windowSet -{nums[i-k]}) + {nums[i]} else windowSet + {nums[i]};
    }
    return false;
}

predicate windowSetValid(nums: seq<int>, k: nat, i: nat, windowSet: set<int>) 
    requires 0 <= i <= |nums|
    requires 0 < k <= |nums|
{
    if i < k then forall x :: x in windowSet ==> x in nums[0..i]
    else forall x :: x in windowSet ==> x in nums[i-k..i]
}

lemma windowSetValidIsSufficient(nums: seq<int>, k: nat, i: nat, windowSet:set<int>)  
    requires 0 <= i < |nums|
    requires 0 < k <= |nums|
    requires windowSetValid(nums, k, i, windowSet)
    requires nums[i] in windowSet
    ensures exists i,j :: 0 <= i < j < |nums| && j-i <= k && nums[i] == nums[j]
{
    if i < k {
        assert nums[i] in windowSet;
        assert forall x :: x in windowSet ==> x in nums[0..i];
    }else{
        assert nums[i] in windowSet;
        assert forall x :: x in windowSet ==> x in nums[i-k..i];
    }
}
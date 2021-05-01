\\predicates to define O(log2n)
predicate IsLog2 (f: nat -> nat)  
{
	exists c :nat, n0: nat :: IsLog2From(c, n0, f)
}
predicate IsLog2From (c :nat, n0: nat, f: nat -> nat)
{
	forall n: nat {:induction n}:: 0 < n0 <= n ==> f(n) <= Log2(n) * c
}
lemma logarithmic (c :nat, n0: nat, f: nat -> nat)
	requires IsLog2From(c, n0, f)
	ensures IsLog2(f)
{}
predicate IsOLog2n (n: nat ,t: nat )
{
	exists h: nat -> nat :: IsLog2(f) && t<=h(n)
}
//help for Ο(log2(n)
function Log2 (x: nat) : nat
	requires x>0
	decreases x
{
	natDivision(x,2);
	if x==1 then 0 else 1+ Log2(x/2)
}
lemma natDivision(a: nat, b: nat)
  requires b>0 
  ensures a/b == (a as real / b as real).Floor
  
{
  assert a == (a / b) * b + (a % b);
  assert a as real == (a / b) as real * b as real + (a % b) as real;
  assert a as real / b as real == (a / b) as real + (a % b) as real / b as real;
}
lemma {:induction x,y}log2Mono (x: nat, y: nat)
	requires x>0 && y>0
	ensures y>=x ==> Log2(y)>=Log2(x)
	decreases x,y 
{
	if (x!=1 && y!=1) { log2Mono(x-1,y-1); }
}		
lemma OLog2nProof(n: nat , t: nat )
	requires n>0
	requires t<=f(n)
	ensures IsOLog2n(n,t)
{
	var c,n0 := logarithmicCalcLemma(n);
	logarithmic(c,n0,f);
}



function f(n: nat) : nat
{
	2*Log2(n+1) + 1
}

//Lemma to prove that binary search time complexity is bounded by 2 + 2*log2(n)	
lemma logarithmicCalcLemma(n: nat)returns(c :nat, n0:nat)
	requires n>0
	ensures IsLog2From(c,n0,f)
{	
	calc <= {
		f(n);
	==
		2*Log2(n+1) + 1;
	<=
		2*Log2(n+1) + Log2(n+1);
	==
		3*Log2(n+1);
	<=  {assert n>=1; log2Mono(n+1,2*n);}
		3*Log2(2*n);
	== 
		3*(1+Log2(n)); 
	}
	assert f(n)<= 3*(1+Log2(n));
	assert n>=2 ==> (f(n)<=6*Log2(n));
	c, n0 := 6, 2;
	assert n>=n0 ==> (f(n)<=c*Log2(n));
	assert IsLog2From(6,2,f);
}



//lopp invariant
predicate BinaryLoop(q: seq<int>,lo: int, hi: int,r: int, key: int)
{
	0<=lo<=hi<=|q| && (r<0 ==> key !in q[..lo] && key !in q[hi..]) && (0<=r ==> r<|q| && q[r]==key)
}

//post condition
predicate BinaryPosts(q: seq<int>,r: int, key: int)
{
	(0<=r ==> r<|q| && q[r]==key) && (r<0 ==> key !in q[..])
}
predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}
//method

method binarySearch(q: seq<int>, key: int) 
    returns (r: int, ghost t: nat)
	requires Sorted(q) 
	ensures BinaryPosts(q, r, key)
	ensures |q|>0 ==> IsOLog2n(|q|, t)
	ensures |q|==0 ==> t==0
{
	t := 0;
	r:= -1;
	if |q|>0
	{
		var lo, hi := 0, |q|;
		while lo < hi
			invariant BinaryLoop(q, lo, hi, r, key)
			invariant t <= TBS(q, 0, |q|, key) - TBS(q, lo, hi, key)
			decreases hi-lo
		{
			var mid := (lo+hi)/2;
			assert (lo+hi)/2 == (lo+((hi-lo)/2));
			if key < q[mid] 
			{
				hi := mid;
			} 
			else if q[mid] < key 
			{
				lo := mid + 1;
			} 
			else 
			{
				r := mid;
				hi := lo;
			}
			t := t+1;
		}
		TBSisLog(q,0,|q|,key);
		log2Mono(|q|,|q|+1);
		OLog2nProof(|q|,t);
	}
}

//recursive Binarysearch function that returns the number of calls we make to the function (binary search time complexity)
function TBS(q: seq<int>,lo: int, hi: int, key: int) : nat
	requires 0 <= lo <= hi <= |q|
	decreases hi-lo
{
	var mid := (lo+hi)/2;
	if (hi-lo==0|||q|==0) then 0 else if  key==q[mid] || (hi-lo==1) then 1 else if key<q[mid] then 1 + TBS(q,lo,mid,key) else 1 + TBS(q,mid+1,hi,key)
}
lemma {:induction q, lo, hi, key}TBSisLog (q: seq<int>,lo: nat, hi: nat, key: int)
	requires |q|>0
	requires 0 <= lo < hi <= |q|
	decreases hi-lo
	ensures TBS(q,lo,hi,key) <= 2*Log2(hi-lo)+1
{
	var mid := (lo+hi)/2;
	if key<q[mid] && 1<hi-lo
	{
		TBSisLog(q,lo,mid,key);
	}
	else if key>q[mid] && hi-lo>2
	{
		log2Mono(hi-(mid+1),(hi-lo)/2);
		TBSisLog(q,mid+1,hi,key);
	}
}

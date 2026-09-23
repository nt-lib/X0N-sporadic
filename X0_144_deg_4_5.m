// We construct X_0(144) as a fiber product of X_0(9) and X_0(16)
// j-map on X_0(9) https://beta.lmfdb.org/ModularCurve/Q/9.12.0.a.1/
// j9 := x^3*(x^3-24)^3 / ((x-3)*(x^2+3*x+9))
// j-map on X_0(8) https://beta.lmfdb.org/ModularCurve/Q/16.24.0.g.1/
// j8 := (y^4-16*y^2+16)^3 / (y^2 * (y-4) * (y+4))


A<x,y> := AffineSpace(GF(5),2);
f :=x^3*(x^3-24)^3*(y^4*(2-y)*(2+y)*(4+y^2)) +(16-16*y^4+y^8)^3*((x-3)*(x^2+3*x+9));
C0 := Curve(A,f);
C := ProjectiveClosure(C0);
F<x,y> := FunctionField(C);



// The following function labels Gal_Q orbits of cusps over any field (even positive characteristic) 
function CuspLabel(c)
    if Evaluate(y^2+4,c) eq 0 then
        l1 := -1;
    elif Valuation(y,c) lt 0 then
        l1 := -2;
    else
        l1 := Integers() ! (Evaluate(y,c)+2);
    end if;
    if Evaluate(x^2+3*x+9,c) eq 0 then
        l2 := -1;
    elif Valuation(x,c) lt 0 then
        l2 := -2;
    else
        l2 := Integers() ! Evaluate(x,c);
    end if;
    return [l1,l2];
end function;

// The following function is a helper function to sum the F_p-cuspidal divisors that are in the same Gal_Q-orbits
function GroupSums(l1, l2)
    A := AssociativeArray();
    for i in [1..#l1] do
        key := l2[i];
        val := l1[i];
        if IsDefined(A, key) then
            A[key] +:= val;
        else
            A[key] := val;
        end if;
    end for;
    return A;
end function;


j := x^3*(x^3-24)^3 / ((x-3)*(x^2+3*x+9));
cusps := Poles(j);
cusp_labels := [CuspLabel(c) : c in cusps];
Q_cusps := [c : c in cusps | #[l : l in cusp_labels | CuspLabel(c) eq l] eq 1];//these are F_5-rational cusps that are reductions of Q-rational cusps
cusp_array := GroupSums(cusps, cusp_labels);
unique_labels := Setseq(Seqset(cusp_labels));
unique_labels := Sort(unique_labels);
cusp_orbits := [cusp_array[l] : l in unique_labels];
time J, JToDiv, DivToJ:= ClassGroup(C);

P0 := Q_cusps[1];
assert Degree(P0) eq 1;
D0 := DivToJ(P0);

Jc, toJ := sub< J | [DivToJ(c)-Degree(c)*D0 : c in cusp_orbits]>;//This is the image of J_C(Q) under reduction modulo 5

//We will now checkt that the number of deg 4 divisors over F_p that map to J_C is equal to the number of Q-rational cuspidal divisors   

plc := [Places(C, i) : i in [1..4]];
divs1111:={SequenceToMultiset([c1,c2,c3,c4]):c1,c2,c3,c4 in plc[1]|DivToJ(c1+c2+c3+c4-4*P0) in Jc};
#divs1111; //237
divs211:={SequenceToMultiset([c1,c2,c3]):c1 in plc[2], c2,c3 in plc[1]|DivToJ(c1+c2+c3-4*P0) in Jc};
#divs211; //152
divs22:={SequenceToMultiset([c1,c2]):c1,c2 in plc[2]|DivToJ(c1+c2-4*P0) in Jc};
#divs22; //11
divs31:={SequenceToMultiset([c1,c2]):c1 in plc[3], c2 in plc[1]|DivToJ(c1+c2-4*P0) in Jc};
#divs31; //0
divs4:={{c1}:c1 in plc[4]|DivToJ(c1-4*P0) in Jc};
#divs4;// 0
//assert #[a:a in cusps| Degree(a) eq 1] eq 12;
//assert #[a:a in cusps| Degree(a) eq 2] eq 6;

assert (#divs1111 + #divs211 + #divs22 + #divs31 + #divs4) eq (Binomial (6+2-1,2) + Binomial(8+4-1,4) + 6*Binomial(8+2-1,2)+1);
//We will now checkt that the number of deg 5 divisors over F_p that map to J_C is equal to the number of Q-rational cuspidal divisors   
/*
Partitions(5);
[
    [ 5 ],
    [ 4, 1 ],
    [ 3, 2 ],
    [ 3, 1, 1 ],
    [ 2, 2, 1 ],
    [ 2, 1, 1, 1 ],
    [ 1, 1, 1, 1, 1 ]
]
*/

plc := [Places(C, i) : i in [1..5]];
divs11111:={SequenceToMultiset([c1,c2,c3,c4,c5]):c1,c2,c3,c4,c5 in plc[1]|DivToJ(c1+c2+c3+c4+c5-5*P0) in Jc};
#divs11111; //1056
divs2111:={SequenceToMultiset([c1,c2,c3,c4]):c1 in plc[2], c2,c3,c4 in plc[1]|DivToJ(c1+c2+c3+c4-5*P0) in Jc};
#divs2111; //544
divs221:={SequenceToMultiset([c1,c2,c3]):c1,c2 in plc[2], c3 in plc[1]|DivToJ(c1+c2+c3-5*P0) in Jc};
#divs221; //88
divs32:={SequenceToMultiset([c1,c2]):c1 in plc[3], c2 in plc[2]|DivToJ(c1+c2-5*P0) in Jc};
#divs32; //0
divs311:={SequenceToMultiset([c1,c2,c3]):c1,c2 in plc[1], c3 in plc[3]|DivToJ(c1+c2+c3-5*P0) in Jc};
#divs311; //0
divs41:={SequenceToMultiset([c1,c2]):c1 in plc[4], c2 in plc[1]|DivToJ(c1+c2-5*P0) in Jc};
#divs41; //0
divs5:={{c1}:c1 in plc[5]|DivToJ(c1-5*P0) in Jc};
#divs5;// 0

assert #divs11111+#divs2111+#divs221+#divs32+#divs311+#divs41+#divs5 eq Binomial(8+5-1,5) + 6*Binomial(8+3-1,3)+Binomial(6+2-1,2)*8+0+0+1*8+0;



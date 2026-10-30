using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class SeparatedPrefixReflectionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Words/Sequenceability/SeparatedPrefixReflection.";
    private static readonly Formula G = X("G"), W = X("w"), C = X("C"),
        Hh = X("h"), K = X("k"), Lo = X("lo"), Hi = X("hi"),
        Nat = X("Nat"), I = X("i"), J = X("j"), A = X("A"),
        Aa = X("a"), Bb = X("b"), T = X("t");
    private static Formula ListG => Call("List", G);
    private static Formula FinsetG => Call("Finset", G);
    private static Formula SetG => Call("Set", G);
    private static Formula P(Formula w, Formula j) => Call("pref", w, j);
    private static Formula V => Call("reverseBlock", W, Hh, K);
    private static Formula Inv(Formula w) => Call("inventory", w);
    private static Formula Int => Call("interior", W, Hh, K);
    private static Formula Ref => Call("reflected", W, Hh, K, Lo, Hi);
    private static Formula Exp => Call("expandAt", V, T, Aa, Bb);
    private static Formula Len(Formula w) => Call("length", w);
    private static Formula Sum(Formula w) => Call("sum", w);
    private static Formula Sep => Call("Separated", C, W, Hh, K, Lo, Hi);
    private static Formula Gap => Sub(Sub(K, Hh), D(1));

    public DocumentDefinition Create()
    {
        var blocks = new System.Collections.Generic.List<DocumentBlock>();
        blocks.Add(Paragraph(Text("All objects live in the original arbitrary additive commutative group. "
            + "The operation reverses actual letters in [h,k), with coefficient one. The affine involution "
            + "x -> lo+hi-x describes prefix values. Separation is required; this is not an unconditional "
            + "group action on all Good orders.")));
        blocks.Add(Definition("pref", "All bounded prefix sums",
            Group(B(Eq(P(W,I),Sum(Call("take",I,W))),("w",ListG),("i",Nat))),
            "Empty and full cuts are included. take and drop take the count first."));
        var interval = Sum(Call("take",Sub(J,I),Call("drop",I,W)));
        var good = B(Imp(And(Lt(I,J),Le(J,Len(W)),Or(Ne(I,D(0)),Ne(J,Len(W)))),
            Ne(interval,D(0))),("i",Nat),("j",Nat));
        blocks.Add(Definition("Good", "Proper zero-sum intervals",
            Group(B(Iff(Call("Good",W),good),("w",ListG))),
            "The full interval alone is exempt, preserving the zero-total convention."));
        var x=X("x"); var y=X("y");
        var cone = And(Not(Call("mem",D(0),C)),B(
            Imp(And(Call("mem",x,C),Call("mem",y,C)),Call("mem",Add(x,y),C)),("x",G),("y",G)));
        blocks.Add(Definition("StrictCone", "Strict additive cone",
            Group(B(Iff(Call("StrictCone",C),cone),("C",SetG))),
            "Only addition closure and exclusion of zero are assumed."));
        blocks.Add(Definition("ConeLE", "Reflexive cone comparison",
            Group(B(Iff(Call("ConeLE",C,x,y),Or(Eq(x,y),Call("mem",Sub(y,x),C))),
                ("C",SetG),("x",G),("y",G))), "Comparison need not be total."));
        var reversed = Call("append",Call("append",Call("take",Hh,W),
            Call("reverse",Call("take",Sub(K,Hh),Call("drop",Hh,W)))),Call("drop",K,W));
        blocks.Add(Definition("reverseBlock", "Actual block reversal",WordBlock(Eq(V,reversed)),
            "Actual occurrence letters are reversed, including endpoint-touching blocks."));
        blocks.Add(Definition("inventory", "All prefix values",Group(B(
            Eq(Inv(W),Call("image",Call("pref",W),Call("range",Add(Len(W),D(1))))),("w",ListG))),
            "A finset records values of every cut, including both endpoint cuts."));
        blocks.Add(Definition("interior", "Removed prefix values",WordBlock(
            Eq(Int,Call("image",Call("pref",W),Call("Ioo",Hh,K)))),
            "Interior cuts of a Good word have distinct values."));
        blocks.Add(Definition("reflected", "Added prefix values",WordBlock(B(
            Eq(Ref,Call("image",Fun("x",G,Sub(Add(Lo,Hi),x)),Int)),("lo",G),("hi",G))),
            "The affine involution is injective by cancellation."));
        var endpoints = Or(And(Eq(P(W,Hh),Lo),Eq(P(W,K),Hi)),
            And(Eq(P(W,Hh),Hi),Eq(P(W,K),Lo)));
        var separation = And(endpoints,Call("ConeLE",C,Lo,Hi),
            B(Imp(And(Lt(Hh,I),Lt(I,K)),Call("mem",Sub(P(W,I),Hi),C)),("i",Nat)),
            B(Imp(And(Le(J,Len(W)),Or(Le(J,Hh),Le(K,J))),Call("ConeLE",C,Lo,P(W,J))),("j",Nat)));
        blocks.Add(Definition("Separated", "Input excursion separation",WordBlock(B(
            Iff(Sep,separation),("lo",G),("hi",G),("C",SetG))),
            "Both endpoint orientations are admitted. Coincident endpoints include the full zero-total case."));
        blocks.Add(ReflectionNode());
        var expanded = Call("append",Call("take",T,W),
            Call("cons",Aa,Call("cons",Bb,Call("drop",Add(T,D(1)),W))));
        blocks.Add(Definition("expandAt", "Prescribed adjacent expansion",Group(B(
            Eq(Call("expandAt",W,T,Aa,Bb),expanded),("w",ListG),("t",Nat),("a",G),("b",G))),
            "At the supplied occurrence of a+b, replace only that occurrence with adjacent a,b."));
        blocks.Add(Definition("compressed", "Same legal-pair alphabet",Group(B(
            Eq(Call("compressed",A,Aa,Bb),Call("insert",Add(Aa,Bb),Call("erase",Call("erase",A,Aa),Bb))),
            ("A",FinsetG),("a",G),("b",G))),
            "Legality makes the merged label new and restores exactly A after expansion."));
        blocks.Add(Definition("Omega", "Actual Good compression space",Group(B(
            Iff(Call("Omega",A,Aa,Bb,W),And(Call("Perm",W,Call("toList",Call("compressed",A,Aa,Bb))),
                Call("Good",W))),("A",FinsetG),("a",G),("b",G),("w",ListG))),
            "Omega consists of actual permutations, with no successful-expansion premise."));
        blocks.Add(RepairNode());
        blocks.AddRange(GenericSupplierNodes());
        blocks.Add(Paragraph(Text("The strict cone is extra structure. A nonempty strict cone cannot exist "
            + "in a finite group, and the nonempty block interior supplies a cone element. This result "
            + "does not settle finite torsion, unrestricted adaptive AM, or the original arbitrary-subset, "
            + "same-M, original-coordinate, coefficient-one parent. The missing global inference is that "
            + "nonempty Omega for every legal pair forces a usable escape for some actual order. No "
            + "universal escape, termination, or H-to-cap implication is proved.")));
        blocks.Add(Paragraph(Text("Provenance: the supplied standalone native separated-block construction "
            + "and independent reconstruction supply the argument. The implementation is repo-prior-exposed "
            + "Codex of the same model family. ChosenMergeExpansionRefutation.Good and expand are specialized "
            + "to ZMod 2 times ZMod 4, and are not generic APIs. BlockSpliceOrdering requires a supplied "
            + "injective cycle and exact chord, absent here. IntegerStrongOrdering, attributed there to "
            + "Kravitz, proves integer existence and does not transform this prescribed compression. "
            + "Pinned Mathlib supplies list splitting, reversal permutation, prefix sums and finset "
            + "cardinality. Its AddGroupCone contains zero; StrictCone here states the required strict "
            + "addition-closed subset instead. No private supplier proof is copied and no literature "
            + "novelty claim is made.")));
        blocks.Add(Paragraph(Text("Escape registration remains unfinished: both exact-telescope "
            + "Reg families compile their four mathematical slots, but the current report records "
            + "declared_unresolved with source.selection_missing. The missing original-occurrence "
            + "source selections are tracked at https://github.com/the-omega-institute/trureturing/issues/21075. "
            + "They are not claimed declared_validated. Independent source review, required CI and "
            + "firstfreeze retain their separate scopes.")));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Separated reflection and repair in the SAME legal compression space.",
            H("Affine prefix geometry on actual words"),Blocks([.. blocks])));
    }

    private static DocumentBlock[] GenericSupplierNodes()
    {
        var l=X("L"); var r=X("R"); var x=X("x");
        var joined=Call("append",l,r);
        var old=Call("append",l,Call("cons",Add(Aa,Bb),r));
        var expanded=Call("append",l,Call("cons",Aa,Call("cons",Bb,r)));
        var prefixGood=B(Imp(And(Lt(I,J),Le(J,Len(W)),Eq(P(W,I),P(W,J))),
            And(Eq(I,D(0)),Eq(J,Len(W)))),("i",Nat),("j",Nat));
        var legalInventory=And(Call("mem",Aa,A),Call("mem",Bb,A),Ne(Aa,Bb),
            Not(Call("mem",Add(Aa,Bb),A)),
            Call("Perm",W,Call("toList",Call("compressed",A,Aa,Bb))),
            Lt(T,Len(W)),Eq(Call("getElem",W,T),Add(Aa,Bb)));
        return [
            Theorem("good_iff","Original proper-interval and prefix equivalence",Group(B(
                Iff(Call("Good",W),prefixGood),("w",ListG))),
                "AdaptiveMergePrefix.good_iff_proper_intervals consumes this original equivalence in reverse. "
                + "Only empty/full equality is exempt, including at zero total."),
            Theorem("pref_append_left","Prefix before an append cut",Group(B(
                Imp(Le(J,Len(l)),Eq(P(joined,J),P(l,J))),
                ("L",ListG),("R",ListG),("j",Nat))),
                "Consumed by AdaptiveMergePrefix.bad_expand_implies_collision to identify a left suffix collision. "
                + "This is the original normalization helper."),
            Theorem("pref_append_right","Prefix after an append cut",Group(B(
                Imp(Le(Len(l),J),Eq(P(joined,J),Add(Sum(l),P(r,Sub(J,Len(l)))))),
                ("L",ListG),("R",ListG),("j",Nat))),
                "Consumed by AdaptiveMergePrefix.bad_expand_implies_collision to identify a right prefix collision. "
                + "Both the append cut and the full cut are included."),
            Theorem("mem_inventory","An inventory value has an actual bounded cut",Group(B(
                Iff(Call("mem",x,Inv(W)),Ex("j",Nat,And(Le(J,Len(W)),Eq(P(W,J),x)))),
                ("w",ListG),("x",G))),
                "AdaptiveMergePrefix.bad_expand_implies_collision consumes the original finite-image equivalence. "
                + "All cuts, including empty and full, are represented."),
            Theorem("expansion_good","A fresh inserted value preserves proper intervals",Group(B(
                Imp(And(Call("Good",old),Not(Call("mem",Add(Sum(l),Aa),Inv(old)))),
                    Call("Good",expanded)),("L",ListG),("R",ListG),("a",G),("b",G))),
                "This original theorem is used contrapositively by AdaptiveMergePrefix.bad_expand_implies_collision. "
                + "It has no separation or strict-cone hypothesis and includes empty sides and zero-total words."),
            Theorem("expansion_inventory","The prescribed expansion restores the original alphabet",Group(B(
                Imp(legalInventory,Call("Perm",Call("expandAt",W,T,Aa,Bb),Call("toList",A))),
                ("A",FinsetG),("a",G),("b",G),("w",ListG),("t",Nat))),
                "AdaptiveMergeRepair.expanded_permutation consumes the original theorem at t = length(L), "
                + "with w = L ++ [a+b] ++ R and the actual LegalPair membership, distinctness and sum-exclusion facts. "
                + "This normalization helper is also used by same_pair_repair.")
        ];
    }

    private static DocumentBlock ReflectionNode()
    {
        var conclusion = And(Call("Perm",V,W),Eq(Len(V),Len(W)),Eq(Sum(V),Sum(W)),
            All("j",Nat,Imp(And(Le(J,Len(W)),Or(Le(J,Hh),Le(K,J))),Eq(P(V,J),P(W,J)))),
            All("j",Nat,Imp(And(Le(Hh,J),Le(J,K)),
                Eq(P(V,J),Sub(Add(P(W,Hh),P(W,K)),P(W,Sub(Add(Hh,K),J)))))),
            Call("Good",V),Call("Disjoint",Ref,Inv(W)),
            Eq(Inv(V),Call("union",Call("sdiff",Inv(W),Int),Ref)),
            Eq(Call("sdiff",Inv(W),Inv(V)),Int),Eq(Call("sdiff",Inv(V),Inv(W)),Ref),
            Eq(Call("card",Int),Gap),Eq(Call("card",Ref),Gap),Lt(D(0),Gap));
        var statement = Group(B(Imp(And(Call("StrictCone",C),Call("Good",W),
            Le(D(2),Sub(K,Hh)),Le(K,Len(W)),Sep),conclusion),
            ("C",SetG),("w",ListG),("h",Nat),("k",Nat),("lo",G),("hi",G)));
        return Theorem("separated_prefix_reflection","Exact reflection and inventory replacement",statement,
            "Split the actual list into L,M,R and reverse M. Summing a prefix of reverse(M) "
            + "gives the suffix sum of M and hence the exact reflection formula. Every old interior "
            + "value is above lo, while every reflected value is below lo. Exterior old values are "
            + "at least lo. Cone closure would put zero in C if a reflected value equaled any old "
            + "value, proving disjointness from the entire old inventory. Old Good gives interior "
            + "injectivity and excludes exterior/interior aliases. Thus the retained exterior set "
            + "is exactly S minus I, and no new cut equality appears. The only surviving possible "
            + "equality is the original empty/full one. This proof covers either endpoint orientation, "
            + "zero total, and endpoint-touching blocks. Reflection and cut reflection are injective, "
            + "so exactly k-h-1 values are removed and added. This is the substantive construction "
            + "consumed immediately by same_pair_repair.");
    }

    private static DocumentBlock RepairNode()
    {
        var result = And(Call("Omega",A,Aa,Bb,V),Ne(V,W),Eq(P(V,T),P(W,T)),
            Ex("q",Lt(T,Len(V)),Eq(Call("getElem",V,T,X("q")),Add(Aa,Bb))),
            Not(Call("mem",Add(P(V,T),Aa),Inv(V))),Call("Good",Exp),
            Call("Perm",Exp,Call("toList",A)),Eq(Sum(Exp),Sum(W)),
            All("x",G,Imp(Call("mem",X("x"),Exp),Ne(X("x"),D(0)))));
        var collision = Ex("i",Nat,And(Lt(Hh,I),Lt(I,K),Eq(Add(P(W,T),Aa),P(W,I))));
        var premises = And(Call("StrictCone",C),Not(Call("mem",D(0),A)),
            Call("mem",Aa,A),Call("mem",Bb,A),Ne(Aa,Bb),
            Not(Call("mem",Add(Aa,Bb),Call("insert",D(0),A))),Call("Omega",A,Aa,Bb,W),
            Lt(T,Len(W)),Eq(Call("getElem",W,T),Add(Aa,Bb)),Le(D(2),Sub(K,Hh)),
            Le(K,Len(W)),Sep,Or(Lt(T,Hh),Le(K,T)),collision);
        var body = B(Imp(premises,result),("C",SetG),("A",FinsetG),("a",G),("b",G),
            ("w",ListG),("t",Nat),("h",Nat),("k",Nat),("lo",G),("hi",G));
        return Theorem("same_pair_repair","Prescribed SAME-pair collision repair",Group(body),
            "Let r=a+b occur at t outside [h,k). Both cuts t and t+1 are exterior, so their "
            + "prefixes are fixed; their difference proves the actual letter at t is still r. "
            + "The prescribed inserted value q=P(t)+a is unchanged and belongs to removed I. "
            + "Exact inventory replacement proves q is absent from the new inventory, rather than "
            + "assuming a successful expansion. Expansion inserts only q into the prefix path. "
            + "All old cut equalities retain the endpoint exception and q collides with none, "
            + "so the expanded word is Good. Permutation cancellation removes the unique new r "
            + "and inserts the original adjacent a,b, proving the exact A inventory, nonzero "
            + "labels and unchanged total. The same compression space and legal pair are retained. "
            + "The collision value witnesses that the new compression differs from the input. "
            + "No Good A-order, desired cycle/inventory, or extra subset induction is supplied.");
    }

    private static Formula B(Formula body,params (string Name,Formula Type)[] binders)
    {
        for(var i=binders.Length-1;i>=0;--i) body=All(binders[i].Name,binders[i].Type,body);
        return body;
    }
    private static Formula Group(Formula body) => Disp(All("G",X("Type"),
        Seq(OpenBracket,Call("AddCommGroup",G),CloseBracket,Sp,body)));
    private static Formula WordBlock(Formula body) => Group(All("w",ListG,
        All("h",Nat,All("k",Nat,body))));
    private static DocumentBlock Definition(string name,string title,Formula formula,string prose) =>
        Node(name,title,formula,prose,DescribeRole.Definition);
    private static DocumentBlock Theorem(string name,string title,Formula formula,string prose) =>
        Node(name,title,formula,prose,DescribeRole.Theorem);
    private static DocumentBlock Node(string name,string title,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("separated-prefix-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner+name),H(title),StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);
    private static Formula X(string x) => F.Id(x);
    private static Formula Call(string x,params Formula[] a) => new Formula.Apply(X(x),[.. a]);
    private static Formula All(string x,Formula t,Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(x),t,b);
    private static Formula Ex(string x,Formula t,Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(x),t,b);
    private static Formula Fun(string x,Formula t,Formula b) => Seq(Operatorname,Grp(X("fun")),Sp,
        Open,X(x),Colon,Sp,t,Close,Sp,Mapsto,Sp,b);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Imp(Formula a,Formula b) => Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b) => Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Or(Formula a,Formula b) => Logic(a,FormulaLogicOperator.Or,b);
    private static Formula Logic(Formula a,FormulaLogicOperator op,Formula b) =>
        new Formula.Logic(Seq(Open,a,Close),op,Seq(Open,b,Close));
    private static Formula And(params Formula[] a)
    {
        var r=a[^1];
        for(var i=a.Length-2;i>=0;--i) r=Logic(a[i],FormulaLogicOperator.And,r);
        return r;
    }
}

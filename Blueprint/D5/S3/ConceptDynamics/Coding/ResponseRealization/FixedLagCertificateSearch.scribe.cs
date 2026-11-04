using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.ResponseRealization;

internal sealed class FixedLagCertificateSearchDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite algorithm decides original numbered certificates at each fixed positive lag.",
        H("Universal fixed-lag certificate search"),
        Blocks(
            Paragraph(Text("The orders n and k and lag m are arbitrary natural numbers. A and B are natural count matrices of orders n and k. The input requires positive orders, positive lag, and a nonzero entry in every row and every column of both matrices. The selector aligned chooses either the two original aligned laws or the two original compatibility sweep laws. All equalities retain the numbered edges and the whole output paths.")),
            D("Maps", "The four actual maps", Raw(Eq(Call("Maps", A, BB, R, S, M), Call("FourEquivalenceFamilies", A, BB, R, S, M))),
                "FourEquivalenceFamilies is the product of the endpoint-indexed families EdgePair(A,R,i,z) ≃ EdgePair(R,B,i,z), EdgePair(B,S,t,w) ≃ EdgePair(S,A,t,w), EdgePair(R,S,i,w) ≃ FinitePath(A,m,i,w), and EdgePair(S,R,t,v) ≃ FinitePath(B,m,t,v). Each equivalence stores its forward and inverse tables and both inverse laws.", DescribeRole.Definition),
            D("Compatible", "Both sweep laws", WithMaps(Eq(Call("Compatible", V), And(Call("ForwardSweepLaw", V), Call("BackwardSweepLaw", V)))),
                "For every length-m A path alpha from i to j and every numbered R edge r from j to z, write psiA(i,j) inverse(alpha)=(u,r0,s0). ForwardSweepLaw says sweep(phiR,alpha,r)=(u,r0,psiB(u,z)(j,s0,r)). BackwardSweepLaw is the literal swapped equation: for a B path beta from t to z and S edge s from z to w, write psiB(t,z) inverse(beta)=(u,s0,r0); sweep(phiS,beta,s)=(u,s0,psiA(u,w)(z,r0,s)). Both quantify over every original path and numbered edge.", DescribeRole.Definition),
            D("Aligned", "Both alignment laws", WithMaps(Eq(Call("Aligned", V), And(Call("AlignedA", Call("phiR", V), Call("phiS", V), Call("psiA", V)), Call("AlignedB", Call("phiR", V), Call("phiS", V), Call("psiB", V))))),
                "AlignedA and AlignedB are the original predicates from OriginalAlignedBalanced, applied to these same four equivalences.", DescribeRole.Definition),
            D("Valid", "Selecting the law pair", WithMaps(All(Eq(Call("Valid", L, V), Call("ifThenElse", L, Call("Aligned", V), Call("Compatible", V))), B("aligned", Id("Bool")))),
                "The true selector requires Aligned and the false selector requires Compatible. No maps are replaced when selecting the laws.", DescribeRole.Definition),
            D("Essential", "Essential count matrices", All(Eq(Call("Essential", Id("X")), And(All(Ex(Neq(Call("entry", Id("X"), Id("i"), Id("j")), Num(0)), B("j", Fin(Id("r")))), B("i", Fin(Id("r")))), All(Ex(Neq(Call("entry", Id("X"), Id("i"), Id("j")), Num(0)), B("i", Fin(Id("r")))), B("j", Fin(Id("r")))))), B("r", Nat), B("X", Mat(Id("r"), Id("r")))),
                "Every row and every column has a nonzero entry. The two clauses are separate, including at order zero.", DescribeRole.Definition),
            D("Input", "The original input boundary", Base(Eq(Call("Input", A, BB, M), Conj(Le(Num(1), N), Le(Num(1), K), Le(Num(1), M), Call("Essential", A), Call("Essential", BB)))),
                "Input consists exactly of 0<n, 0<k, 0<m and essentiality of A and B. Lag zero, an empty order, and a zero row or column are rejected.", DescribeRole.Definition),
            D("OriginalExists", "Unrestricted original existence", Selected(Eq(Call("OriginalExists", A, BB, M, L), And(Call("Input", A, BB, M), Ex(Call("Valid", L, V), B("R", Mat(N, K)), B("S", Mat(K, N)), B("d", Call("Maps", A, BB, R, S, M)))))),
                "R and S range over all natural matrices of the displayed shapes. There is no entry bound in this existence predicate. The witness includes all four equivalences and both selected laws.", DescribeRole.Definition),
            D("MatrixLaws", "The four matrix products", Raw(Eq(Call("MatrixLaws", A, BB, R, S, M), Conj(Eq(Multiply(A,R), Multiply(R,BB)), Eq(Multiply(BB,S), Multiply(S,A)), Eq(Multiply(R,S), Call("power",A,M)), Eq(Multiply(S,R), Call("power",BB,M))))),
                "The four products follow from cardinalities of the four equivalences. The RS and SR equations use the corresponding A and B path counts separately.", DescribeRole.Definition),
            D("BoundedMatrix", "A finite matrix carrier", All(Eq(Call("BoundedMatrix", Id("r"), Id("s"), Id("bound")), Call("FiniteMatrixFunctions", Id("r"), Id("s"), Call("succ", Id("bound")))), B("r",Nat), B("s",Nat), B("bound",Nat)),
                "BoundedMatrix(r,s,bound) is Fin r → Fin s → Fin(bound+1), including entries zero through bound.", DescribeRole.Definition),
            D("entries", "Recovering natural entries", All(Eq(Call("entry",Call("entries",Id("X")),Id("i"),Id("j")),Call("val",Call("entry",Id("X"),Id("i"),Id("j")))), B("r",Nat), B("s",Nat), B("bound",Nat), B("X",Call("BoundedMatrix",Id("r"),Id("s"),Id("bound"))), B("i",Fin(Id("r"))), B("j",Fin(Id("s")))),
                "The decoding takes each Fin value's natural-number value without changing a row, column or edge number.", DescribeRole.Definition),
            D("Candidate", "All bounded matrices and all maps", Base(Eq(Call("Candidate", A, BB, M), Call("BoundedMatrixAndMapTuples", A, BB, M))),
                "The dependent sum first enumerates R in BoundedMatrix(n,k,powerMaximum(A,m)), then S in BoundedMatrix(k,n,powerMaximum(B,m)), then all Maps(A,B,entries(R),entries(S),m). Path types are encoded recursively. Equivalences are encoded by their actual forward and inverse finite tables with inverse-law tests. Thus the enumeration includes whole maps rather than cardinality surrogates.", DescribeRole.Definition),
            D("candidateCheck", "Checking a candidate", Selected(All(Eq(Call("candidateCheck", A, BB, M, L, Id("c")), Call("decide", Conj(Call("Input", A, BB, M), Call("CandidateMatrixLaws", A, BB, M, Id("c")), Call("Valid", L, Call("maps", Id("c")))))), B("c", Call("Candidate", A, BB, M)))),
                "CandidateMatrixLaws abbreviates MatrixLaws(A,B,entries(c.R),entries(c.S),m). The final conjunction tests both laws of the selected kind on c's four actual maps.", DescribeRole.Definition),
            D("search", "Executable finite search", Selected(Eq(Call("search",A,BB,M,L), Call("GuardedFirstAcceptedCandidate", A,BB,M,L))),
                "If Input is false, search returns none. Otherwise it runs List.find? with candidateCheck on Encodable.sortedUniv(Candidate(A,B,m)). A successful result returns the actual bounded matrices and all four equivalences. Both Fintype and Encodable are constructed, so this is executable exhaustive search.", DescribeRole.Definition),
            D("existsBool", "The decision Boolean", Selected(Eq(Call("existsBool",A,BB,M,L), Call("isSome",Call("search",A,BB,M,L)))),
                "existsBool observes whether the search returned an actual candidate.", DescribeRole.Definition),
            D("search_sound", "Soundness of the returned maps", Selected(All(Imp(Eq(Call("search",A,BB,M,L),Call("some",Id("c"))), And(Call("Input",A,BB,M),Call("Valid",L,Call("maps",Id("c"))))), B("c",Call("Candidate",A,BB,M)))),
                "List.find? supplies a true candidateCheck. Eliminating its decidable conjunction gives the original input and both selected laws for precisely the returned maps.", DescribeRole.Theorem),
            D("search_correct", "Universal correctness", Selected(Iff(Eq(Call("existsBool",A,BB,M,L),Id("true")),Call("OriginalExists",A,BB,M,L))),
                "Soundness recovers the unrestricted witness from the returned candidate. For completeness, start with arbitrary natural R and S and the original four equivalences. Essentiality and the inverse path bijections bound every R entry by powerMaximum(A,m) and every S entry by powerMaximum(B,m). Encode each entry in the corresponding Fin type and retain the same four equivalences. This constructs an actual Candidate whose check is true; membership in sortedUniv makes the search succeed. The construction occurs directly in the universal theorem and adds no bounded-input hypothesis.", DescribeRole.Theorem),
            Paragraph(Text("The executable examples use command-local CountMat(1,1) inputs with every entry equal to one, evaluate both selectors, and reject lag zero and a nonessential input. The utility instance names the already existing private unitCountMatrix in CompatibleResponseForgettingBound, which is the same closed one-matrix input. A separate example enumerates all four map tables for the one-vertex two-loop input. Examples provide computational observations, not additional mathematical results.")))));

    private static DocumentBlock.Describe D(string name,string title,Formula formula,string proof,DescribeRole role) => Describe.Lean(
        DescribeId.Create("fixedlagcertificatesearch-" + name.ToLowerInvariant().Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch." + name), H(title),
        StatementSource.FromAuthor(FormulaDsl.Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(proof))), role);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll,[..v],p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[..v],p);
    private static Formula Eq(Formula a,Formula b) => Equal(a,b);
    private static Formula Neq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Conj(params Formula[] p) { var v=p[^1]; for(var i=p.Length-2;i>=0;--i)v=And(p[i],v); return v; }
    private static Formula Nat => Id("Nat"); private static Formula N=>Id("n"); private static Formula K=>Id("k"); private static Formula M=>Id("m");
    private static Formula A=>Id("A"); private static Formula BB=>Id("B"); private static Formula R=>Id("R"); private static Formula S=>Id("S"); private static Formula V=>Id("d"); private static Formula L=>Id("aligned");
    private static Formula Fin(Formula r)=>Call("Fin",r); private static Formula Mat(Formula r,Formula s)=>Call("CountMat",r,s);
    private static Formula Base(Formula p)=>All(p,B("n",Nat),B("k",Nat),B("A",Mat(N,N)),B("B",Mat(K,K)),B("m",Nat));
    private static Formula Selected(Formula p)=>Base(All(p,B("aligned",Id("Bool"))));
    private static Formula Raw(Formula p)=>Base(All(p,B("R",Mat(N,K)),B("S",Mat(K,N))));
    private static Formula WithMaps(Formula p)=>Raw(All(p,B("d",Call("Maps",A,BB,R,S,M))));
}

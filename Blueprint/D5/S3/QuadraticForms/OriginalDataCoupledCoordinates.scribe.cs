using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class OriginalDataCoupledCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One coordinate realization of the original observation lift couples the symplectic split, the positive energy blocks, the canonical permutation, and both Williamson normal forms.",
        H("The full coupled observation-compatible coordinate theorem"),
        Blocks(Describe.Lean(
            DescribeId.Create("original-data-coupled-coordinates"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/OriginalDataCoupledCoordinates.original_data_coupled_coordinates"),
            H("Original data and one shared coordinate realization"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For a natural number m, I_m is Fin m plus Fin m and C_m is the real functions on I_m. The block index I_k plus I_h represents C_k times C_h by Sum.elim. Write Jplus_m=[[0,I],[-I,0]]=-Matrix.J (Fin m) real. The first half of each Darboux basis is labelled q and the second p because its inl/inr pairing is positive delta. Matrix(e) always means the standard-coordinate matrix of the displayed linear equivalence e.")),
                Paragraph(Text("The only hypotheses are the original positive definite S, surjective O, closure O(Jplus_n S)=KO, and the original strict bounds 0<r<2n. Define P=OS-inverse O-transpose, L=S-inverse O-transpose P-inverse, U=range L, and V=ker O. No invertibility, complementarity, nondegeneracy, evenness, invariant lift, or coordinate basis is assumed.")),
                Paragraph(Text("The result is one inhabitant of CoupledCoordinates S O. All eight groups below refer to the same fields of that inhabitant. Choose one such inhabitant and keep it fixed throughout all the displays. The typed witnesses and all clauses below are read together for this one inhabitant, not as separate existential choices. P,L,Sv,Sh,Jb,Dv,Dh,W,Pi,e and iota are definitionally fixed abbreviations, not additional premises or independently chosen replacements.")),
                new DocumentBlock.Section(H("Typed witnesses and fixed definitions"), Blocks(
                    [.. Displays(WitnessTypes()), .. Displays(Dimensions()), .. Displays(Definitions())])),
                new DocumentBlock.Section(H("C1–C3: original images and actual coordinate equivalences"), Blocks([
                .. Displays(C123()),
                Paragraph(Text("Apply original_data_symplectic_retract to the original S,O,K. Its restricted-radical argument tests x in ker O against (Jplus_n S)x; the vanishing pairing is negative strictly positive energy unless x=0. That argument remains on the live dependency path to the two returned Darboux bases. Include their vectors in the ambient space to obtain the columns of Tv and Th. The supplier Basis.equivFun gives their coordinate equivalences onto exactly U and V. Compose the visible equivalence with the bridge's actual observation restriction to get B. The supplier Submodule.prodEquivOfIsCompl assembles T from these same two basis maps. The returned dimension equalities and the strict bounds imply k,h>0."))])),
                new DocumentBlock.Section(H("C4–C5: symplectic and energy congruences for the same T"), Blocks([
                .. Displays(C45()),
                Paragraph(Text("Read the Darboux pairings as matrix entries. Alternation gives the reverse inr/inl pairing with a minus sign, producing Jplus in both diagonal blocks. The bridge identifies the exact symplectic orthogonal U-perp with V, giving the upper-right zero block; transposition and skew symmetry give the lower-left zero block. Its energy orthogonality gives the upper-right energy zero block; symmetry of S gives the lower-left block. Positive congruence with the injective Tv and Th proves positivity of exactly Sv=Tv-transpose S Tv and Sh=Th-transpose S Th. The original lift satisfies L-transpose S=P-inverse O and OL=I, hence L-transpose S L=P-inverse. Substitution of Tv=LB proves Sv=B-transpose P-inverse B."))])),
                new DocumentBlock.Section(H("C6–C7: canonical ordering and every covector"), Blocks([
                .. Displays(PermutationDefinitions()),
                .. Displays(C67()),
                Paragraph(Text("The mode concatenation e sends a visible index to the first k entries and a hidden index to the following h entries, followed by the equality n=k+h. The index map iota sends block order (qv,pv,qh,ph) to global order (qv,qh,pv,ph). Pi is the 0/1 matrix with entry one exactly when iota(i)=j. It acts on coordinate functions by composition with iota. Reindexing the identity matrix proves both inverse identities and identifies the inverse linear equivalence's matrix with Pi-transpose. Reindexing Jplus gives Pi-transpose Jb Pi=Jplus_n. Transposing OT=[B,0] proves the covector identity for every a, and composition with Pi gives its permuted version."))])),
                new DocumentBlock.Section(H("C8: the two exact Williamson applications and one final R"), Blocks([
                .. Displays(C8()),
                Paragraph(Text("Apply the existing positive_definite_williamson separately to exactly Sv and Sh. Retain the actual returned Wv,Wh and strictly positive frequency functions nuv,nuh. Their symplectic membership gives invertibility, so the block map W is a linear equivalence. Define Bhat=BWv, That=TW, and R=That Pi as actual compositions of equivalences. Surjectivity of Wv and Wh preserves range Tv and range Th. Multiplication preserves TvWv=L Bhat and the observation identity. Block multiplication gives the exact two diagonal energy blocks, and the fixed Pi gives the displayed global energy. The final covector formula uses the transpose of this same R, not a separately chosen global Williamson map."))])),
                Paragraph(Text("The bridge retains arbitrary n,r and empty/full endpoints. The existing Darboux, complement, permutation and Williamson constructions support empty finite indices; only the present strict-bound consumer concludes k,h>0. Covectors transform by R-transpose when z=Rx. No displacement transformation, physical implementation, metaplectic operator, tensor product, Gibbs state, or thermal assertion is part of the result."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var assumptions = And(Call("PosDef", V("S")), Call("Surjective", Call("mulVec", V("O"))),
            Equal(Mul(V("O"), J("n"), V("S")), Mul(V("K"), V("O"))),
            Lt(D(0), V("r")), Lt(V("r"), Multiply(D(2), V("n"))));
        var body = Seq(Paren(assumptions), Sp, Rightarrow, Sp,
            Call("Nonempty", Call("CoupledCoordinates", V("S"), V("O"))));
        return All(V("n"), Nat, All(V("r"), Nat,
            All(V("S"), Mat(I("n"), I("n")),
            All(V("O"), Mat(Call("Fin", V("r")), I("n")),
            All(V("K"), Mat(Call("Fin", V("r")), Call("Fin", V("r"))), body)))));
    }

    private static Formula[] WitnessTypes()
    {
        var witnesses = new (string, Formula)[] {
            ("k", Nat), ("h", Nat),
            ("Tv", Mat(I("n"), I("k"))), ("Th", Mat(I("n"), I("h"))),
            ("B", LE(C("k"), Obs)), ("T", LE(Block, C("n"))),
            ("Wv", Mat(I("k"), I("k"))), ("Wh", Mat(I("h"), I("h"))),
            ("nuv", Arrow(Call("Fin", V("k")), Real)),
            ("nuh", Arrow(Call("Fin", V("h")), Real)),
            ("Bhat", LE(C("k"), Obs)), ("That", LE(Block, C("n"))),
            ("R", LE(C("n"), C("n"))),
            ("P", Mat(Call("Fin", V("r")), Call("Fin", V("r")))),
            ("L", Mat(I("n"), Call("Fin", V("r")))),
            ("Sv", Mat(I("k"), I("k"))), ("Sh", Mat(I("h"), I("h"))),
            ("Jb", Mat(BI, BI)), ("Dv", Mat(I("k"), I("k"))),
            ("Dh", Mat(I("h"), I("h"))), ("W", Mat(BI, BI)),
            ("e", Call("Equiv", Call("Sum", Call("Fin", V("k")), Call("Fin", V("h"))), Call("Fin", V("n")))),
            ("iota", Call("Equiv", BI, I("n"))), ("Pi", Mat(BI, I("n"))),
            ("PiEquiv", LE(C("n"), Block))
        };
        return [.. witnesses.Select(witness =>
            Seq(V(witness.Item1), Sp, Colon, Sp, witness.Item2))];
    }

    private static Formula[] Dimensions() =>
    [
        Equal(V("r"), Multiply(D(2), V("k"))),
        Equal(V("n"), Add(V("k"), V("h"))),
        Lt(D(0), V("k")), Lt(D(0), V("h"))
    ];

    private static Formula[] Definitions() =>
    [
        Equal(V("P"), Mul(V("O"), Inv(V("S")), Tr(V("O")))),
        Equal(V("L"), Mul(Inv(V("S")), Tr(V("O")), Inv(V("P")))),
        Equal(V("Sv"), Mul(Tr(V("Tv")), V("S"), V("Tv"))),
        Equal(V("Sh"), Mul(Tr(V("Th")), V("S"), V("Th"))),
        Equal(V("Jb"), Diag(J("k"), J("h"))),
        Equal(V("Dv"), Diag(Call("diagonal", V("nuv")), Call("diagonal", V("nuv")))),
        Equal(V("Dh"), Diag(Call("diagonal", V("nuh")), Call("diagonal", V("nuh")))),
        Equal(V("W"), Diag(V("Wv"), V("Wh")))];

    private static Formula[] C123() =>
    [
        Call("Injective", Call("mulVec", V("Tv"))), Call("Injective", Call("mulVec", V("Th"))),
        Equal(Range(V("Tv")), Range(V("L"))), Equal(Range(V("Th")), Ker(V("O"))),
        Equal(Mul(V("O"), V("Tv")), M("B")), Equal(Mul(V("O"), V("Th")), D(0)),
        Equal(V("Tv"), Mul(V("L"), M("B"))),
        All(V("xv"), C("k"), All(V("xh"), C("h"),
            Equal(Call("T", Pair(V("xv"), V("xh"))), Add(MV(V("Tv"), V("xv")), MV(V("Th"), V("xh")))))),
        Equal(M("T"), Col(V("Tv"), V("Th"))),
        Equal(Mul(V("O"), M("T")), Col(M("B"), D(0)))];

    private static Formula[] C45() =>
    [
        Equal(Mul(Tr(V("Tv")), J("n"), V("Tv")), J("k")),
        Equal(Mul(Tr(V("Th")), J("n"), V("Th")), J("h")),
        Equal(Mul(Tr(V("Tv")), J("n"), V("Th")), D(0)),
        Equal(Mul(Tr(V("Th")), J("n"), V("Tv")), D(0)),
        Equal(Mul(Tr(M("T")), J("n"), M("T")), V("Jb")),
        Call("PosDef", V("Sv")), Call("PosDef", V("Sh")),
        Equal(Mul(Tr(V("Tv")), V("S"), V("Th")), D(0)),
        Equal(Mul(Tr(V("Th")), V("S"), V("Tv")), D(0)),
        Equal(V("Sv"), Mul(Tr(M("B")), Inv(V("P")), M("B"))),
        Equal(Mul(Tr(M("T")), V("S"), M("T")), Diag(V("Sv"), V("Sh")))];

    private static Formula[] PermutationDefinitions() =>
    [
        Equal(V("e"), Call("modeConcat", V("n"), V("k"), V("h"))),
        Equal(V("iota"), Call("blockToGlobal", V("n"), V("k"), V("h"))),
        Equal(V("PiEquiv"), Call("canonicalPiEquiv", V("n"), V("k"), V("h"))),
        All(V("i"), BI, All(V("j"), I("n"), Equal(Call("entry", V("Pi"), V("i"), V("j")),
            Call("if", Equal(Call("iota", V("i")), V("j")), D(1), D(0))))),
        All(V("z"), C("n"), Equal(MV(V("Pi"), V("z")), Pair(
            Pair(Lam("i", Call("Fin", V("k")), Call("z", Call("inl", Call("e", Call("inl", V("i")))))),
                 Lam("i", Call("Fin", V("k")), Call("z", Call("inr", Call("e", Call("inl", V("i"))))))),
            Pair(Lam("i", Call("Fin", V("h")), Call("z", Call("inl", Call("e", Call("inr", V("i")))))),
                 Lam("i", Call("Fin", V("h")), Call("z", Call("inr", Call("e", Call("inr", V("i"))))))))))];

    private static Formula[] C67() =>
    [
        Equal(M("PiEquiv"), V("Pi")), Equal(Call("matrix", Call("symm", V("PiEquiv"))), Tr(V("Pi"))),
        Equal(Mul(Tr(V("Pi")), V("Pi")), D(1)), Equal(Mul(V("Pi"), Tr(V("Pi"))), D(1)),
        Equal(Mul(Tr(V("Pi")), V("Jb"), V("Pi")), J("n")),
        Equal(Mul(Tr(Mul(M("T"), V("Pi"))), J("n"), Mul(M("T"), V("Pi"))), J("n")),
        All(V("a"), Obs, Equal(MV(Tr(M("T")), MV(Tr(V("O")), V("a"))),
            Pair(MV(Tr(M("B")), V("a")), D(0)))),
        All(V("a"), Obs, Equal(MV(Tr(Mul(M("T"), V("Pi"))), MV(Tr(V("O")), V("a"))),
            MV(Tr(V("Pi")), Pair(MV(Tr(M("B")), V("a")), D(0)))))];

    private static Formula[] C8() =>
    [
        Call("Member", V("Wv"), Call("symplecticGroup", Call("Fin", V("k")), Real)),
        Call("Member", V("Wh"), Call("symplecticGroup", Call("Fin", V("h")), Real)),
        All(V("i"), Call("Fin", V("k")), Lt(D(0), Call("nuv", V("i")))),
        All(V("i"), Call("Fin", V("h")), Lt(D(0), Call("nuh", V("i")))),
        Equal(Mul(Tr(V("Wv")), J("k"), V("Wv")), J("k")),
        Equal(Mul(Tr(V("Wh")), J("h"), V("Wh")), J("h")),
        Equal(Mul(Tr(V("Wv")), V("Sv"), V("Wv")), V("Dv")),
        Equal(Mul(Tr(V("Wh")), V("Sh"), V("Wh")), V("Dh")),
        Equal(M("Bhat"), Mul(M("B"), V("Wv"))), Equal(M("That"), Mul(M("T"), V("W"))),
        All(V("xv"), C("k"), All(V("xh"), C("h"),
            Equal(Call("That", Pair(V("xv"), V("xh"))),
                Add(MV(Mul(V("Tv"), V("Wv")), V("xv")), MV(Mul(V("Th"), V("Wh")), V("xh")))))),
        Equal(M("R"), Mul(M("That"), V("Pi"))),
        Equal(Range(Mul(V("Tv"), V("Wv"))), Range(V("L"))),
        Equal(Range(Mul(V("Th"), V("Wh"))), Ker(V("O"))),
        Equal(Mul(V("Tv"), V("Wv")), Mul(V("L"), M("Bhat"))),
        Equal(Mul(V("O"), M("That")), Col(M("Bhat"), D(0))),
        Equal(Mul(Tr(M("That")), J("n"), M("That")), V("Jb")),
        Equal(Mul(Tr(M("That")), V("S"), M("That")), Diag(V("Dv"), V("Dh"))),
        Equal(Mul(Tr(M("R")), J("n"), M("R")), J("n")),
        Equal(Mul(Tr(M("R")), V("S"), M("R")), Mul(Tr(V("Pi")), Diag(V("Dv"), V("Dh")), V("Pi"))),
        All(V("a"), Obs, Equal(MV(Tr(M("That")), MV(Tr(V("O")), V("a"))),
            Pair(MV(Tr(V("Wv")), MV(Tr(M("B")), V("a"))), D(0)))),
        All(V("a"), Obs, Equal(MV(Tr(M("R")), MV(Tr(V("O")), V("a"))),
            MV(Tr(V("Pi")), Pair(MV(Tr(V("Wv")), MV(Tr(M("B")), V("a"))), D(0)))))];

    private static DocumentBlock[] Displays(params Formula[] clauses) =>
        [.. clauses.Select(clause => new DocumentBlock.DisplayFormula(Disp(clause)))];

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula I(string n) => Call("Sum", Call("Fin", V(n)), Call("Fin", V(n)));
    private static Formula C(string n) => Arrow(I(n), Real);
    private static Formula BI => Call("Sum", I("k"), I("h"));
    private static Formula Block => Arrow(BI, Real);
    private static Formula Obs => Arrow(Call("Fin", V("r")), Real);
    private static Formula J(string n) => Seq(Minus, Call("MatrixJ", Call("Fin", V(n)), Real));
    private static Formula M(string name) => Call("matrix", V(name));
    private static Formula Mat(Formula i, Formula j) => Call("Matrix", i, j, Real);
    private static Formula LE(Formula x, Formula y) => Call("LinearEquiv", Real, x, y);
    private static Formula Arrow(Formula x, Formula y) => Paren(Seq(x, Sp, To, Sp, y));
    private static Formula Tr(Formula x) => Call("transpose", x);
    private static Formula Inv(Formula x) => Call("inv", x);
    private static Formula Mul(params Formula[] xs) => xs.Aggregate((a, b) => Multiply(a, b));
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula MV(Formula x, Formula y) => Call("mulVec", x, y);
    private static Formula Col(Formula x, Formula y) => Call("columns", x, y);
    private static Formula Pair(Formula x, Formula y) => Call("SumElim", x, y);
    private static Formula Diag(Formula x, Formula y) => Call("fromBlocks", x, D(0), D(0), y);
    private static Formula Range(Formula x) => Call("range", Call("mulVecLin", x));
    private static Formula Ker(Formula x) => Call("ker", Call("mulVecLin", x));
    private static Formula Lt(Formula x, Formula y) => Seq(x, Sp, F.Lt, Sp, y);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(F.LambdaLower, Sp, Paren(Seq(V(name), Sp, Colon, Sp, type)), Dot, Sp, body);
    private static Formula Paren(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Paren(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(params Formula[] terms) => Seq(
        [.. terms.SelectMany((term, i) => i == 0
            ? new[] { Paren(term) } : new[] { Sp, Land, Sp, Paren(term) })]);
}

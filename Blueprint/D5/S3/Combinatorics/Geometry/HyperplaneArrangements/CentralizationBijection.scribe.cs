using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.HyperplaneArrangements;

internal sealed class CentralizationBijectionDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/chenfuliwang2026centralization");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, "A first-residue-preserving CRT bijection for integral affine arrangements.",
            "evidence-not-specified-by-formal-manifest", Anchor.ParseCanonical("mathlib/module/Mathlib.Data.ZMod.Basic")),
        H("Centralization convolution over coprime residue rings"),
        Blocks(
            Paragraph(Text("Chen, Fu, Li and Wang, arXiv:2606.00599v1 (v1 submitted 30 May 2026), §4.2, printed p. 17, ask for "
                + "a natural CRT bijection interpreting Corollary 1.2. Its indexing flats are the "
                + "linear flats of the centralization. Theorem 4.6 of §4.2 instead treats Wang's "
                + "convolution indexed by affine flats of the original arrangement.")),
            Definition("centralization-row", "row", "Integral row evaluation",
                "For an index type I and n coordinates, ring R, a : I → Fin n → ℤ, "
                + "i in I and x : Fin n → R, row R a i x is the sum over Fin n of "
                + "the product of the cast of a(i,j) to R and x(j)."),
            Definition("centralization-kernel", "commonKernel", "Rational common kernel",
                "For any finite row subset S, commonKernel a S is the rational submodule of "
                + "Fin n → ℚ consisting of exactly the vectors v with row ℚ a i v = 0 "
                + "for every i in S."),
            Definition("centralization-rational-flat", "RationalFlat", "Actual rational flats",
                "RationalFlat a is the subtype of rational submodules K of Fin n → ℚ "
                + "for which there exists S : Finset I with commonKernel a S = K."),
            Definition("centralization-complement", "Complement", "Concrete affine complement",
                "Complement a b m is the subtype of vectors z : Fin n → ZMod m with "
                + "row (ZMod m) a i z different from the cast of b(i) for every i in I."),
            Describe.Lean(DescribeId.Create("centralization-crt-bijection-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Exact bijection and first residue"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For arbitrary universe u, the index type I has type Type u. "
                        + "Finite(I) is the original Finite instance, and n is the coordinate dimension. "
                        + "Rows(I,n) is I → Fin n → ℤ and Constants(I) is I → ℤ. "
                        + "The row evaluation over a ring R is the sum over Fin n of the integer "
                        + "coefficient cast to R times the corresponding coordinate. "
                        + "C(a,b,m) is Complement a b m, the subtype of vectors in (ℤ/mℤ)^n "
                        + "whose row evaluations differ from the cast of b(i) for every i in I.")),
                    Paragraph(Text("FiberSum(a,b,p,q) is the dependent sum over RationalFlat a, "
                        + "the actual rational submodules of Fin n → ℚ equal to common kernels "
                        + "of finite row sets. For each such V let J(V) contain exactly those i "
                        + "whose rational row evaluation vanishes at every v in V. The first fibre "
                        + "is the subtype of x in (ℤ/pℤ)^n with row(a,i,x) different from b(i) "
                        + "for every i in J(V). The second is the subtype of y in (ℤ/qℤ)^n with "
                        + "row(a,i,y)=0 for every i in J(V) and row(a,i,y) different from 0 "
                        + "for every i outside J(V). The fibre is their product. "
                        + "Equiv denotes the actual equivalence of types with both inverse laws. "
                        + "First(e(z),j) is (e z).2.1.val j and Value(z,j) is z.val j. "
                        + "Cast(p,q,t) is ZMod.cast from ZMod(p*q) to ZMod p at t.")),
                    Paragraph(Text("D is positive and is chosen from a and b before p and q. "
                        + "The proof constructs integer certificates for rational affine consistency "
                        + "and rational homogeneous implication of every subsystem. A rational point "
                        + "gives a denominator certificate, while an inconsistent direction gives "
                        + "an integer separating functional. The finite product of the requisite "
                        + "positive integers is coprime to every good modulus. The homogeneous "
                        + "implication also controls the exact zero rows of modular points.")),
                    Paragraph(Text("Split z by CRT as (x,zq), choose a solution c(x) modulo q "
                        + "of the affine equations hit at x modulo p, and subtract c(x) "
                        + "from zq to obtain y. The exact homogeneous zero rows of y yield the "
                        + "rational common-kernel flat. An affine equation hit by x is hit by zq "
                        + "exactly when its homogeneous row vanishes at y. Inversion adds the same "
                        + "c(x) and applies inverse CRT. The rational flat equivalence reindexes "
                        + "the strata and preserves the underlying first vector. Both inverse laws "
                        + "and the literal first-residue equation are checked.")),
                    Paragraph(Text("Integral minors compute the same ranks over ℚ and ℝ, so "
                        + "the rational and real flats correspond by extension of scalars and have the same row closures. "
                        + "Definition 2.4 identifies J(V) with the affine localization rows. "
                        + "A nonzero restriction to a linear flat is surjective over the field. "
                        + "Homogeneous implication good reduction identifies the reduced flat "
                        + "independently of the chosen finite generators and detects proper restrictions.")),
                    Paragraph(Text("Any valid family of centers gives this construction. The checked "
                        + "implementation uses Classical.choose. Choosing the lexicographically least "
                        + "solution in coordinate order with residues 0 through q−1 gives a deterministic "
                        + "variant mathematically, since each solution set is finite and nonempty. "
                        + "The argument covers composite coprime moduli.")),
                    Paragraph(Text("Taking cardinalities gives the exact complement count identity. "
                        + "The source's Proposition 4.4 evaluates characteristic polynomials for "
                        + "positive m greater than the arrangement-specific threshold qA and "
                        + "coprime to its period ρA. Lemma 4.5 identifies the reductions of affine "
                        + "subarrangements and restrictions. Use these results for A at pq, "
                        + "the affine localizations at p, and the centralization and its central "
                        + "restrictions at q, with integral coordinates on the rational flats "
                        + "compatible with reduction. For a real integral hyperplane arrangement, "
                        + "it suffices that coprime p and q each exceed the maximum of 1 and the "
                        + "applicable thresholds and each be coprime to the product of D, the "
                        + "applicable periods and the coordinate factors. This also suffices at pq. "
                        + "The Lean endpoint proves the complement equivalence. Characteristic-polynomial "
                        + "evaluation follows from the cited counting results."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Statement()
    {
        Formula I = V("I"), n = V("n"), a = V("a"), b = V("b"), d = V("D");
        Formula p = V("p"), q = V("q"), e = V("e"), z = V("z"), j = V("j");
        Formula complement = Call("C", a, b, Mul(p, q));
        Formula fibres = Call("FiberSum", a, b, p, q);
        Formula first = Equal(Call("First", new Formula.Apply(e, [z]), j),
            Call("Cast", p, q, Call("Value", z, j)));
        Formula equivalence = Ex("e", Call("Equiv", complement, fibres),
            All("z", complement, All("j", Call("Fin", n), first)));
        Formula goodModuli = All("p", Nat(), All("q", Nat(),
            Imp(Less(D(1), p), Imp(Less(D(1), q),
                Imp(Call("Coprime", p, q), Imp(Call("Coprime", p, d),
                    Imp(Call("Coprime", q, d), equivalence)))))));
        Formula bound = Ex("D", Nat(), And(Less(D(0), d), goodModuli));
        return All("u", Call("UniverseLevel"), All("I", Call("Type", V("u")), All("n", Nat(),
            Imp(Call("Finite", I), All("a", Call("Rows", I, n),
                All("b", Call("Constants", I), bound))))));
    }
}

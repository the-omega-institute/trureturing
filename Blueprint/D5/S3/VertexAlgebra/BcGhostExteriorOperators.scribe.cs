using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostExteriorOperatorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostExteriorOperators.";
    private static Formula Quantifiers() => Seq(
        Forall, Sp, F.Id("K"), Colon, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("CommRing", F.Id("K")), CloseBracket, Comma, Sp,
        Forall, Sp, F.Id("i"), InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
        Forall, Sp, F.Id("v"), InMacro, Sp, Call("Fock", F.Id("K")), Comma, Esc);
    private static Formula Coordinates(Formula state) => Call("E", F.Id("K"), state);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed-subset creation and deletion are the coordinates of actual exterior multiplication and contraction.",
        H("Exterior Realization of the Infinite Ghost Carrier"),
        Blocks(
            Paragraph(Text("For any commutative ring K, let V be the free K-module with basis e_i "
                + "indexed by all natural numbers. Fock(K) consists of finite K-linear combinations "
                + "of finite subsets S of the natural numbers. E is the linear equivalence taking "
                + "the coordinate vector at S to the product of the exterior generators e_i in "
                + "increasing order. Its existence uses Mathlib's exterior-algebra basis and its "
                + "representation equivalence, including the empty product and the zero ring.")),
            Paragraph(Text("Creation inserts i when it is absent and is zero otherwise. Deletion "
                + "erases i when it is present and is zero otherwise. Both operations carry the "
                + "factor (-1) raised to the number of elements of S smaller than i. The one-particle "
                + "coordinate functional epsilon_i evaluates a vector at i; delta_i denotes "
                + "Mathlib's left contraction by epsilon_i.")),
            Describe.Lean(
                DescribeId.Create("bc-ghost-exterior-create"),
                DeclarationHandle.Create(Prefix + "exterior_create"),
                H("Signed creation intertwines exterior multiplication"),
                StatementSource.FromAuthor(Disp(Seq(Quantifiers(),
                    Coordinates(Call("create", F.Id("i"), F.Id("v"))), Eq,
                    Call("iota", F.Id("K"), Call("e", F.Id("i"))), Sp,
                    Coordinates(F.Id("v"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every commutative ring K, natural i and state v, "
                    + "E(create(i)v) equals iota_K(e_i) * E(v), i.e. E(v) left-multiplied "
                    + "by iota_K(e_i). "
                    + "Induction by the least element of a subset computes the insertion parity. "
                    + "Passing a generator across the least element uses the exterior "
                    + "anticommutation identity; repeated generators have square zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-exterior-annihilate"),
                DeclarationHandle.Create(Prefix + "exterior_annihilate"),
                H("Signed deletion intertwines actual contraction"),
                StatementSource.FromAuthor(Disp(Seq(Quantifiers(),
                    Coordinates(Call("annihilate", F.Id("i"), F.Id("v"))), Eq,
                    Call("delta", F.Id("K"), F.Id("i"), Coordinates(F.Id("v")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every commutative ring K, natural i and state v, "
                    + "E(annihilate(i)v) equals delta_i(E(v)). The contraction recurrence "
                    + "delta_i(iota(e_a)x)=epsilon_i(e_a)x-iota(e_a)delta_i(x) computes "
                    + "the deletion sign, and linearity extends it to every finite superposition. "
                    + "Consequently the actual signed operators inherit Mathlib's CAR and "
                    + "supply the ghost stress-current commutators on the same carrier."))),
                DescribeRole.Theorem),
            Paragraph(Text("These are exact algebraic coordinates on an infinite mode set. "
                + "No finite truncation, characteristic-zero hypothesis or positive inner product "
                + "is used. The result concerns fermionic operators; it does not establish "
                + "Virasoro central charge, BRST cohomology, string amplitudes or spacetime dynamics.")))));
}

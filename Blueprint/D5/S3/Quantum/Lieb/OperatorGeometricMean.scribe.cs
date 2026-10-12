using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class OperatorGeometricMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed reusable operator API: OperatorGeometricMean.",
        H("OperatorGeometricMean"),
        Blocks(
            Paragraph(Text("Consumed Apache-2.0 Physlib source at immutable revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and "
                + "Hayata Yamasaki. Retire each supplier when an equivalent consumed declaration is "
                + "available in the repository-pinned Mathlib.")),
            Describe.Lean(
                DescribeId.Create("positive-operator-power-mean-concavity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/OperatorGeometricMean.operatorPowerMean_jointlyConcaveOn_pdSet"),
                H("Joint concavity of the operator power mean"),
                StatementSource.FromAuthor(EndpointFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(
                    Paragraph(Text("The carrier is a nontrivial complete complex Hilbert space. Both exponents alpha,beta "
                        + "belong to [0,1], including endpoints. The operatorPowerMean is the generalized "
                        + "perspective with f(x)=x^alpha and h(x)=x^beta.")),
                    Paragraph(Text("Both inputs are self-adjoint with strictly positive real spectra. The mean is jointly "
                        + "concave under a common mixture coefficient, with no A/B commutation and no "
                        + "finite-dimensionality requirement. This endpoint has PD inputs in both positions; "
                        + "PSD-first/PD-second belongs to the consumed generalized-perspective theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-operator-power-mean-convexity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/OperatorGeometricMean.operatorPowerMean_jointlyConvexOn_pdSet"),
                H("Joint convexity of the operator power mean"),
                StatementSource.FromAuthor(ConvexEndpointFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(Paragraph(Text("The exact Physlib supplier at original line 89 "
                    + "has alpha in [1,2] and beta in [0,1], including all endpoints, "
                    + "on every complete nontrivial complex Hilbert space. Both "
                    + "inputs are strictly positive; no commutation or finite "
                    + "dimension is assumed. The source proof is retained, with "
                    + "its uniform power condition supplied by the consumed "
                    + "PowerConvexity adapter. LiebAndoTrace consumes this endpoint "
                    + "at beta=1. This is attributed reuse, not new mathematics."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)) };
        if (arguments.Length == 0) return Seq([.. items]);
        items.Add(Open);
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Instance(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula U => F.Id("u");
    private static Formula Carrier => F.Id("H");
    private static Formula UnitInterval => Call("Icc", D(0), D(1));
    private static Formula HilbertPrefix(bool nontrivial = true, bool finite = false,
        bool complete = true)
    {
        var items = new List<Formula> {
            Forall, Sp, U, Colon, Sp, Call("Level"), Comma, Esc,
            Carrier, Colon, Sp, Call("Type", U), Comma, Esc,
            Instance("NormedAddCommGroup", Carrier), Comma, Sp,
            Instance("InnerProductSpace", ComplexType, Carrier), Comma, Sp };
        if (complete) items.AddRange([Instance("CompleteSpace", Carrier), Comma, Sp]);
        if (nontrivial) items.AddRange([Instance("Nontrivial", Carrier), Comma, Sp]);
        if (finite) items.AddRange([Instance("FiniteDimensional", ComplexType, Carrier), Comma, Sp]);
        return Seq([.. items]);
    }
    private static Formula Conjunction(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var i = 0; i < clauses.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(clauses[i]);
        }
        return Seq([.. items]);
    }

    private static Formula ConvexEndpointFormula() => Disp(Seq(
        HilbertPrefix(), Alpha, Comma, Sp, Beta, Colon, Sp, RealType, Comma, Esc,
        Conjunction(Seq(Alpha, Sp, InMacro, Sp, Call("Icc", D(1), D(2))),
            Seq(Beta, Sp, InMacro, Sp, UnitInterval)), Sp, Implies, Sp,
        Call("JointlyConvexOn", Call("pdSet", Carrier), Call("pdSet", Carrier),
            Call("operatorPowerMean", Carrier, Alpha, Beta)), Dot));

    private static Formula EndpointFormula() => Disp(Seq(
        HilbertPrefix(), Alpha, Comma, Sp, Beta, Colon, Sp, RealType, Comma, Esc,
        Conjunction(Seq(Alpha, Sp, InMacro, Sp, UnitInterval),
            Seq(Beta, Sp, InMacro, Sp, UnitInterval)), Sp, Implies, Sp,
        Call("JointlyConcaveOn", Call("pdSet", Carrier), Call("pdSet", Carrier),
            Call("operatorPowerMean", Carrier, Alpha, Beta)), Dot));
}

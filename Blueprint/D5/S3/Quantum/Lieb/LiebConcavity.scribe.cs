using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class LiebConcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed Lieb joint trace concavity for positive-definite inputs and interior exponents.",
        H("LiebConcavity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ando-strict-pd-convexity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/LiebConcavity.liebTrace_jointlyConvexOn_pdSet"),
                H("Joint trace convexity on positive-definite pairs"),
                StatementSource.FromAuthor(ConvexEndpointFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(Paragraph(Text("This is the exact Physlib endpoint from original "
                    + "line 1118, with unchanged proof text, arbitrary K and "
                    + "1 <= s <= 2. TracePerspectiveConvexity consumes this "
                    + "interface. The carrier is a complete nontrivial finite "
                    + "complex Hilbert space, and both inputs have strictly "
                    + "positive spectra. Neither K invertibility nor A/B "
                    + "commutation is assumed. Its operator-power and perspective "
                    + "suppliers come from the same immutable pin."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lieb-strict-pd-concavity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/LiebConcavity.liebTrace_jointlyConcaveOn_pdSet"),
                H("Joint trace concavity on positive-definite pairs"),
                StatementSource.FromAuthor(EndpointFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(
                    Paragraph(Text("The exponent s satisfies 0 < s < 1. The carrier is a nontrivial "
                        + "complete finite-dimensional complex Hilbert space. K is arbitrary; A and B "
                        + "are self-adjoint with strictly positive spectra. Original A and B need "
                        + "not commute. Both arguments use the same convex-mixture coefficient.")),
                    Paragraph(Text("The unchanged attributed supplier proof evaluates a jointly "
                        + "concave Hilbert-Schmidt operator perspective against the adjoint of K. "
                        + "The left and right multiplication operators commute for arbitrary A and B. "
                        + "The real trace functional is defined in the consumed bridge module.")),
                    Paragraph(Text("Use s = 1 - p, exchange the input arguments, and apply trace "
                        + "cyclicity to obtain the interior-exponent positive-definite form with "
                        + "the adjoint of K, A to exponent p, K and B to exponent 1 - p in that order. "
                        + "The retained endpoint has this strict-PD and interior-exponent scope.")),
                    Paragraph(Text("A separate transient exact application was compiled for every "
                        + "finite decidable index type d, including the empty type. For arbitrary "
                        + "complex d-by-d K, positive-semidefinite A1, A2, B1, B2, and p and t in "
                        + "[0,1], put T_p(A,B) = Re Tr(K* A^p K B^(1-p)). Then "
                        + "(1-t) T_p(A1,B1) + t T_p(A2,B2) is at most "
                        + "T_p((1-t) A1 + t A2, (1-t) B1 + t B2). Original A and B "
                        + "need not commute. Here the powers are the spectral CFC powers, "
                        + "with A^0 = I for positive-semidefinite A.")),
                    Paragraph(Text("The matrix-to-Euclidean-operator star algebra equivalence "
                        + "preserves powers and traces. For 0 < p < 1, applying the supplier to "
                        + "A + epsilon I and B + epsilon I and taking epsilon down to zero uses "
                        + "the pinned CFC continuity for positive powers on the full PSD cone. "
                        + "At p = 0 and p = 1 the functional is linear in B and A respectively. "
                        + "An empty index type has zero trace. The exact full application passed "
                        + "Lean compilation and a scoped compiled report with only propext, "
                        + "Classical.choice and Quot.sound; its source and evidence are retained "
                        + "in the persistent operator-perspective-lieb-continuation-20261011 "
                        + "research directory. Its temporary D5 source is removed after validation "
                        + "because the application is reuse rather than an independent new result.")),
                    Paragraph(Text("This is reuse of the Apache-2.0 Physlib source at revision "
                        + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, "
                        + "Kento Mori and Hayata Yamasaki. Lieb's theorem is known; no mathematical "
                        + "originality is claimed. The selected transient trace-equivalence "
                        + "bridge credits Alex Meiburg and retains its MIT notice and license."))),
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
    private static Formula Operators => Call("L", Carrier);
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
        HilbertPrefix(finite: true), F.Id("s"), Colon, Sp, RealType, Comma, Sp,
        F.Id("K"), Colon, Sp, Operators, Comma, Esc,
        Conjunction(Seq(D(1), Sp, Le, Sp, F.Id("s")),
            Seq(F.Id("s"), Sp, Le, Sp, D(2))), Sp, Implies, Sp,
        Call("JointlyConvexOn", Call("pdSet", Carrier), Call("pdSet", Carrier),
            Call("liebTraceMap", Carrier, F.Id("s"), F.Id("K"))), Dot));

    private static Formula EndpointFormula() => Disp(Seq(
        HilbertPrefix(finite: true), F.Id("s"), Colon, Sp, RealType, Comma, Sp,
        F.Id("K"), Colon, Sp, Operators, Comma, Esc,
        Conjunction(Seq(D(0), Sp, Lt, Sp, F.Id("s")),
            Seq(F.Id("s"), Sp, Lt, Sp, D(1))), Sp, Implies, Sp,
        Call("JointlyConcaveOn", Call("pdSet", Carrier), Call("pdSet", Carrier),
            Call("liebTraceMap", Carrier, F.Id("s"), F.Id("K"))), Dot));
}

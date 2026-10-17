// Source candidate; current Scribe compilation and emission are pending.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class PositiveMapJensenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proposed finite positive-map Jensen bridge; no compilation or admission claim.",
        H("PositiveMapJensen"), Blocks(
            Describe.Lean(DescribeId.Create("rectangular-cfc"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/PositiveMapJensen.cfc_intertwining"),
                H("Rectangular spectral intertwining"), StatementSource.FromAuthor(Intertwining()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For finite complex matrix carriers n and m, Hermitian A and B, "
                    + "and arbitrary rectangular V satisfying A V = V B, every real "
                    + "function f satisfies cfc(f,A) V = V cfc(f,B). Every function "
                    + "is continuous on a finite matrix spectrum. The coefficient "
                    + "proof is extracted from the existing local rectangularCFCAmbient "
                    + "argument in CanonicalChannelDPI; it is needed as a public "
                    + "interface for the sum-carrier dilation and support localization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-unital-map-jensen"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/PositiveMapJensen.positive_unital_jensen"),
                H("Jensen for every finite positive unital complex-linear map"),
                StatementSource.FromAuthor(Jensen()), SupplierProvenance(), Blocks(Paragraph(Text(
                    "Let n and m be arbitrary finite decidable carriers in Type u, "
                    + "Phi a complex-linear positive map from M_n(C) to M_m(C) with "
                    + "Phi(I)=I, and A PSD. Assume OperatorConvexOnAll.{u} (Ici 0) f "
                    + "and ContinuousOn f (Ici 0). Then cfc(f,Phi(A)) <= Phi(cfc(f,A)). "
                    + "The spectral projections E_i of A give positive effects "
                    + "Phi(E_i), whose sum is I, so finite effect Jensen applies. "
                    + "Apply that result first to f-f(0), then restore constants "
                    + "by unitality. The consumed private dilation first stacks "
                    + "sqrt(F_i) on the product carrier k times m, with Gram I; "
                    + "the rectangular isometry is then the upper-right block "
                    + "of an endomorphism contraction on n plus m. Intertwining "
                    + "identifies both CFC compressions. The intermediate supplier "
                    + "CondIciAll includes f(0)<=0; subtracting f(0) discharges "
                    + "that condition. There is no sign restriction on f(0), no "
                    + "complete-positivity hypothesis, and no trace assumption. "
                    + "An empty output carrier is trivial; an empty input with a "
                    + "nonempty output contradicts unitality.")), Paragraph(Text(
                    "Both the Lean and this Scribe document are uncompiled source "
                    + "proposals. No validated information-audit "
                    + "registration, kernel result, official acceptance or novelty "
                    + "claim is supplied by this document."))), DescribeRole.Theorem))));

    private static AssessedProvenance SupplierProvenance() => AssessedProvenance.FromRepo(
        LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb"));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Intertwining() => Seq(
        Call("Hermitian", F.Id("A")), Comma, Sp, Call("Hermitian", F.Id("B")), Comma, Sp,
        F.Id("A"), F.Id("V"), Eq, F.Id("V"), F.Id("B"), Implies, Esc,
        Call("cfc", F.Id("f"), F.Id("A")), F.Id("V"), Eq,
        F.Id("V"), Call("cfc", F.Id("f"), F.Id("B")));
    private static Formula Jensen() => Seq(
        Call("OperatorConvexOnAll", Call("Ici", D(0)), F.Id("f")), Comma, Sp,
        Call("ContinuousOn", F.Id("f"), Call("Ici", D(0))), Comma, Sp,
        Call("PositiveComplexLinear", F.Id("Phi")), Comma, Sp,
        Call("Phi", D(1)), Eq, D(1), Comma, Sp, D(0), Le, F.Id("A"), Implies, Esc,
        Call("cfc", F.Id("f"), Call("Phi", F.Id("A"))), Le,
        Call("Phi", Call("cfc", F.Id("f"), F.Id("A"))));
}

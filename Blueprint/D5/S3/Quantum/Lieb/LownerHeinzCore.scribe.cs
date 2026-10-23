using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class LownerHeinzCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed general C-star power convexity with its consumed integral proof.",
        H("LownerHeinzCore"),
        Blocks(
            Paragraph(Text("This module is a consumed supporting source transplant for the "
                + "Lieb-Ando trace curvature endpoints and their general power supplier. "
                + "Its definitions and proof steps come from Kei Tsukamoto, Kento Mori and "
                + "Hayata Yamasaki's Apache-2.0 Physlib source at immutable revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142. The Lean file records the exact "
                + "original module and retained supplier license. No mathematical originality "
                + "is claimed.")),
            Describe.Lean(DescribeId.Create("general-power-convexity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici"),
                H("General C-star power convexity on the positive cone"),
                StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(
            Paragraph(Text("The source-owning power_Icc_one_two_operatorConvexOn_Ici "
                + "is the exact Physlib endpoint at original line 1785. Its "
                + "convexOn_nnrpow_Ioo_one_add supplier is at line 1427. The "
                + "consumed slice preserves arbitrary ordered C-star algebras, "
                + "Nontrivial and NonnegSpectrumClass, the entire positive cone "
                + "including singular inputs, both exponent endpoints and "
                + "noncommuting products. The shifted-inverse input calls pinned "
                + "Mathlib convexOn_ringInverse_algebraMap_add; its CFC rewrite "
                + "is the only compatibility adapter. The positivity helper "
                + "calls the existing IsSelfAdjoint.conjugate_nonneg API.")),
            Paragraph(Text("PowerConvexity consumes this theorem to preserve the "
                + "general ConvexOn interface, including the trivial algebra, "
                + "and the uniform Jensen condition. No new general power proof "
                + "or originality is claimed."))),
                DescribeRole.Theorem))));

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
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket);
    private static Formula Endpoint()
    {
        var a = F.Id("A"); var p = F.Id("p");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Sp,
            a, Colon, Sp, Call("Type", F.Id("u")), Comma, Esc,
            Instance("CStarAlgebra", a), Comma, Sp, Instance("PartialOrder", a), Comma, Sp,
            Instance("StarOrderedRing", a), Comma, Sp, Instance("Nontrivial", a), Comma, Sp,
            Instance("NonnegSpectrumClass", real, a), Comma, Esc,
            p, Colon, Sp, real, Comma, Sp, D(1), Sp, Le, Sp, p, Sp, Le, Sp, D(2),
            Sp, Implies, Esc,
            Call("OperatorConvexOn", Call("Ici", D(0)),
                Seq(Lambda, Sp, F.Id("x"), Mapsto, Call("rpow", F.Id("x"), p))));
    }
}

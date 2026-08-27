using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class FiniteInformationalEffectCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Informationally complete quantum effects admit a dimension-bounded finite certificate.",
        H("Finite Informational Effect Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-informational-effect-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PredictionDepth/FiniteInformationalEffectCertificate."
                        + "finite_informational_effect_certificate"),
                H("A finite effect subfamily retains informational completeness"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source family consists of positive Hermitian effects bounded "
                            + "above by the identity. Its trace readout is injective on the "
                            + "canonical positive trace-one density states.")),
                    Paragraph(Text(
                        "Canonical trace removal turns informational completeness into full "
                            + "span of the real trace-zero Hermitian carrier. Finite-dimensional "
                            + "basis extraction chooses source indices rather than replacement "
                            + "vectors, so the selected original effects still separate states."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula CertificateFormula()
    {
        Formula d = F.Id("d");
        Formula index = F.Id("I");
        Formula effectFamily = F.Id("E");
        Formula effect = F.Id("A");
        Formula selected = F.Id("S");
        Formula rho = Rho;
        Formula i = F.Id("i");
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula hermitian = Call("HermitianSpace", d);
        Formula traceZero = Call("traceZeroHermitian", d);
        Formula effectMatrix = Call("matrix", effect);
        Formula effectType = Seq(
            OpenBrace, effect, Colon, Sp, hermitian, Sp, Mid, Sp,
            Call("PosSemidef", effectMatrix), Sp, Land, Sp,
            Call("PosSemidef", Seq(D(1), Minus, effectMatrix)), CloseBrace);
        Formula effectAt = Apply(effectFamily, i);
        Formula rawReadout = Seq(
            Open, rho, Colon, Sp, Call("DensityState", Call("Fin", d)), Sp,
            Mapsto, Sp, Open, i, Colon, Sp, index, Sp, Mapsto, Sp,
            Re, Sp, Call("Tr", Seq(Call("matrix", rho), Sp,
                Call("matrix", effectAt))), Close, Close);
        Formula selectedIndex = Seq(i, InMacro, Sp, selected);
        Formula centeredSet = Seq(
            OpenBrace,
            Call("centeredHermitianMap", d, effectAt), Colon, Sp,
            selectedIndex, CloseBrace);
        Formula selectedReadout = Seq(
            Open, rho, Colon, Sp, Call("DensityState", Call("Fin", d)), Sp,
            Mapsto, Sp, Open, selectedIndex, Sp, Mapsto, Sp,
            Re, Sp, Call("Tr", Seq(Call("matrix", rho), Sp,
                Call("matrix", effectAt))), Close, Close);
        Formula dimensionBound = Seq(new Formula.Power(d, D(2)), Minus, D(1));

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, nat, Comma, Sp, Call("NeZero", d), Comma,
            RowBreak, Grp(),
            index, Colon, Sp, type, Comma, RowBreak, Grp(),
            effectFamily, Colon, Sp, index, Sp, To, Sp, effectType, Comma,
            RowBreak, Grp(),
            Call("Injective", rawReadout), Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, selected, Colon, Sp, Call("Finset", index), Comma, Sp,
            Call("card", selected), Sp, Leq, Sp, dimensionBound, Sp, Land,
            RowBreak, Grp(),
            Call("span", real, centeredSet), Sp, Eq, Sp, traceZero, Sp, Land,
            RowBreak, Grp(),
            Call("Injective", selectedReadout), Dot));
    }
}

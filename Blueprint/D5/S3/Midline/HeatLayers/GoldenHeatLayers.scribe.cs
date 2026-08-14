using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.HeatLayers;

internal sealed class GoldenHeatLayersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden heat spectrum splits into prime layers whose convergence abscissae strictly decrease to zero, so the abscissa of the whole trace is set by the ground layer alone.",
        H("Layers of the Golden Heat Spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-euler-exponents-are-strictly-increasing"),
                DeclarationHandle.Create("D5/S3/Midline/HeatLayers/GoldenHeatLayers.o5_beta_strictMono"),
                H("The golden Euler exponents are strictly increasing"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("u"), Sp, Lt, Sp, F.Id("v"), Sp, Implies, Sp,
                    Operatorname, Grp(F.Id("o5Beta")), Open, F.Id("u"), Close, Sp,
                    Lt, Sp,
                    Operatorname, Grp(F.Id("o5Beta")), Open, F.Id("v"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The closed form of the exponent account separates a linear term from a fractional part, and the linear increment exceeds the largest possible swing of that fractional part; strict monotonicity follows on consecutive indices."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("each-golden-layer-has-a-boundary-divergent-abscissa"),
                DeclarationHandle.Create("D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_layer_boundary_divergent"),
                H("Each golden layer has a boundary-divergent abscissa"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("BoundaryDivergentAbscissa")), Open,
                    Operatorname, Grp(F.Id("goldenLayer")), Open, F.Id("k"), Close, Comma, Sp,
                    Frac, Grp(D(1)),
                    Grp(Operatorname, Grp(F.Id("o5Beta")), Open,
                        F.Id("k"), Plus, D(1), Close), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every layer index the prime series converges strictly to the right of the reciprocal exponent, diverges strictly to its left, and diverges on the boundary itself, where the layer reduces to the reciprocals of the primes."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("layer-abscissae-strictly-decrease"),
                DeclarationHandle.Create("D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_layer_abscissa_strictAnti"),
                H("The layer abscissae strictly decrease"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("j"), Comma, Sp, F.Id("k"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("j"), Sp, Lt, Sp, F.Id("k"), Sp, Implies, Sp,
                    Frac, Grp(D(1)),
                    Grp(Operatorname, Grp(F.Id("o5Beta")), Open,
                        F.Id("k"), Plus, D(1), Close), Sp,
                    Lt, Sp,
                    Frac, Grp(D(1)),
                    Grp(Operatorname, Grp(F.Id("o5Beta")), Open,
                        F.Id("j"), Plus, D(1), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Strict monotonicity of the exponents inverts to strict antitonicity of their reciprocals, so a higher layer always converges strictly further to the left."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("layer-abscissae-tend-to-zero"),
                DeclarationHandle.Create("D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_layer_abscissa_tendsto_zero"),
                H("The layer abscissae tend to zero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Tendsto")), Open,
                    F.Id("k"), Sp, Mapsto, Sp,
                    Frac, Grp(D(1)),
                    Grp(Operatorname, Grp(F.Id("o5Beta")), Open,
                        F.Id("k"), Plus, D(1), Close), Comma, Sp,
                    Operatorname, Grp(F.Id("atTop")), Comma, Sp,
                    Operatorname, Grp(F.Id("nhds")), Open, D(0), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The linear lower bound on the exponent account drives the exponents to infinity along the layer index, so their reciprocals converge to zero; no layer abscissa is ever attained at zero."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("every-excited-layer-lies-strictly-left-of-the-ground-abscissa"),
                DeclarationHandle.Create("D5/S3/Midline/HeatLayers/GoldenHeatLayers.golden_excited_layer_abscissa_lt"),
                H("Every excited layer lies strictly left of the ground abscissa"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("k"), Sp, Implies, Sp,
                    Frac, Grp(D(1)),
                    Grp(Operatorname, Grp(F.Id("o5Beta")), Open,
                        F.Id("k"), Plus, D(1), Close), Sp,
                    Lt, Sp,
                    Frac, Grp(D(1)), Grp(Varphi, Caret, Grp(D(2))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ground layer carries the abscissa one over phi squared, and every excited layer sits strictly to its left. The abscissa of the full two-parameter trace is therefore fixed by the ground layer alone: every excited layer still converges at that threshold, so the divergence pinning the trace's abscissa is witnessed by the ground layer by itself."))),
                DescribeRole.Theorem
            ))));
}

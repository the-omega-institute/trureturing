using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Signed;

internal sealed class CandidateSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Gaussian sources and the spatial T equation",
        H("Signed Gaussian sources and the spatial T equation"),
        Blocks(
            Describe.Lean(DescribeId.Create("h"), DeclarationHandle.Create(Prefix + "h"),
                H("Signed source factor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Boolean label e and complex u and r, h(e,u,r) is "
                    + "1 − (1 − r)u for true (positive) and 1 − r − u for false (negative). "
                    + "Write b(u) = 1 − u for the common factor."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
                H("Normalized source root"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("W(e,u,r) is h(e,u,r) times the original signed sourceMode(e,u,r). "
                    + "The mode sum fixes the root."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rho"), DeclarationHandle.Create(Prefix + "rho"),
                H("Signed J numerator factor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Boolean e and f and complex u and v, ρ(e,f,u,v) equals u + v "
                    + "for equal labels and −(1 + uv) for mixed labels."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("k"), DeclarationHandle.Create(Prefix + "K"),
                H("Signed T denominator factor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Boolean pairs (++), (+−), (−+), (−−), respectively, "
                    + "K(e,f,u,v) is uv, −u, −v, or 1 in the original complex coordinates u and v."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("e"), DeclarationHandle.Create(Prefix + "E"),
                H("Signed T denominator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("E(e,f,u,v,r) = b(u)b(v) − rK(e,f,u,v). "
                    + "In particular the negative pair uses b(u)b(v) − r."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("n"), DeclarationHandle.Create(Prefix + "N"),
                H("Signed T numerator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the same sign order (++), (+−), (−+), (−−), "
                    + "N(e,f,u,v,r) is 1 + (1 − r)uv, −((1 − r)u + v), −(u + (1 − r)v), "
                    + "or 1 − r + uv, respectively."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rational-t"), DeclarationHandle.Create(Prefix + "rationalT"),
                H("Rational T factor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each sign pair and complex u, v and r, the factor is "
                    + "rN/(2E) + r²uv/E², with N and E evaluated at (e,f,u,v,r)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("candidate-t"), DeclarationHandle.Create(Prefix + "candidateT"),
                H("Signed T candidate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product of the original sourceMode(e,u,r) and sourceMode(f,v,r) "
                    + "multiplies the difference rationalT(e,f,u,v,r) − correction(r), where correction(r) = r(1 − r)ℓ(r) "
                    + "and ℓ is the logarithmic derivative of the original half-binomial period."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("candidate-j"), DeclarationHandle.Create(Prefix + "candidateJ"),
                H("Regular signed J candidate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two original sourceMode factors multiply "
                    + "r/4 − correction(r) + r²ρ(e,f,u,v)/(4b(u)b(v)(W(e,u,r) + W(f,v,r))²). "
                    + "This expression is regular on the source bidisk, including the same-sign diagonal."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("beta"), DeclarationHandle.Create(Prefix + "beta"),
                H("Literal frequency coefficient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For complex u, β(e,u) equals (1 − 3u)/2 for the positive label "
                    + "and −(u + 1)/2 for the negative label, as in the original slice operators."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("l"), DeclarationHandle.Create(Prefix + "L"),
                H("Signed slice operator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F : ℂ → ℂ, L(e,F,u) = u b(u) deriv(F,u) + β(e,u)F(u). "
                    + "On slices of the original kernel it gives the corresponding literal mode derivative."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mode-d"), DeclarationHandle.Create(Prefix + "modeD"),
                H("Signed D contribution"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The D term is −ru/h(e,u,r) at the positive label and +ru/h(e,u,r) "
                    + "at the negative label. In the original mode convention, "
                    + "modeH(e,u,r,λ) = modeD(e,u,r) − modeA(e,u,r) − 2r modeScale(e,u)λ, "
                    + "with modeScale equal to 1 for true and u for false."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-argument"),
                DeclarationHandle.Create(Prefix + "normalizedArgument"),
                H("Argument of the normalized root"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For complex u and r, the argument is 1 + ru/b(u) for the positive label "
                    + "and 1 − r/b(u) for the negative label. On ‖u‖ + ‖r‖ < 1 it equals h(e,u,r)/b(u) "
                    + "and has strictly positive real part."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("h-ne-zero"), DeclarationHandle.Create(Prefix + "h_ne_zero"),
                H("Signed source factor is nonzero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean e and complex u and r with ‖u‖ + ‖r‖ < 1, "
                    + "h(e,u,r) ≠ 0 by the corresponding branch of the original mode-factor bounds."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("source-u"), DeclarationHandle.Create(Prefix + "source_u"),
                H("Derivative of the original signed source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean e and complex u and r with ‖u‖ + ‖r‖ < 1, the map "
                    + "w ↦ sourceMode(e,w,r) has complex derivative mLog(e,u,r) sourceMode(e,u,r) at u. "
                    + "Here mLog = 1/(2b(u)) + slope(e,r)/(2h(e,u,r)), with slope 1 − r for true "
                    + "and 1 for false. The proof uses the original explicit mode derivative."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("source-frequency"), DeclarationHandle.Create(Prefix + "source_frequency"),
                H("Signed source frequency multiplier"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean e and complex u and r with b(u) ≠ 0 and h(e,u,r) ≠ 0, "
                    + "u b(u)mLog(e,u,r) + β(e,u) = modeA(e,u,r). Substitution into the product rule "
                    + "recovers the original modeA coefficient."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("w-square"), DeclarationHandle.Create(Prefix + "W_square"),
                H("Square of the normalized source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean e and complex u and r with ‖u‖ + ‖r‖ < 1, "
                    + "W(e,u,r)² = h(e,u,r)/b(u), using the square of the original sourceMode."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("source-w-normalization"),
                DeclarationHandle.Create(Prefix + "source_W_normalization"),
                H("Original source and root normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean e and complex u and r with ‖u‖ + ‖r‖ < 1, "
                    + "sourceMode(e,u,r) b(u) W(e,u,r) = 1. This identity gives the reciprocal source "
                    + "factors used in the J chart cancellation."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("w-sum-ne-zero"), DeclarationHandle.Create(Prefix + "W_sum_ne_zero"),
                H("The two normalized roots cannot cancel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all Boolean e and f and complex u, v and r with ‖u‖ + ‖r‖ < 1 "
                    + "and ‖v‖ + ‖r‖ < 1, W(e,u,r) + W(f,v,r) ≠ 0. The original generator sum identifies "
                    + "each W with the principal half-power of its normalized argument by combining powers "
                    + "at that same base. Both roots have positive real part."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("ell-eq-source"), DeclarationHandle.Create(Prefix + "ell_eq_source"),
                H("Period derivative in the original source convention"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For complex r with ‖r‖ < 1, ℓ(r) equals "
                    + "OriginalGaussianAllIndexResolvent.shiftedCentralDerivative(r,0)/period(r). "
                    + "Identify the zero-shift central series with the original period and use its existing "
                    + "derivative before dividing by the period."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("e-ne-zero"), DeclarationHandle.Create(Prefix + "E_ne_zero"),
                H("The T denominator is nonzero on the source domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all Boolean e and f and complex u, v and r with "
                    + "‖u‖ + √‖r‖ < 1 and ‖v‖ + √‖r‖ < 1, E(e,f,u,v,r) ≠ 0. "
                    + "The sign table gives ‖K‖ ≤ 1, while each b factor has norm greater than √‖r‖. "
                    + "Consequently ‖rK‖ < ‖b(u)b(v)‖."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("candidate-t-original-displacement"),
                DeclarationHandle.Create(Prefix + "candidateT_original_displacement"),
                H("Signed T displacement with the original source"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For all Boolean e and f, complex u and v, and real 0 < r < 1 with "
                        + "‖u‖ + √r < 1 and ‖v‖ + √r < 1, set x = (r : ℂ), "
                        + "λ = shiftedCentralDerivative(x,0)/period(x), and C(u,v) = candidateT(e,f,u,v,x). "
                        + "The difference modeScale(f,v)L(e,C(·,v),u) − modeScale(e,u)L(f,C(u,·),v) equals "
                        + "(1 − x) sourceMode(e,u,x) sourceMode(f,v,x) "
                        + "[modeA(e,u,x)modeH(f,v,x,λ) − modeH(e,u,x,λ)modeA(f,v,x)]/2.")),
                    Paragraph(Text("The rational differentiation gives the alternating A and D combination "
                        + "in that order. The period correction converts it to the alternating A and H "
                        + "combination with the original λ. The source inequalities give the nonzero "
                        + "denominators, including on the axes and diagonal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("candidate-j-joint-analytic"),
                DeclarationHandle.Create(Prefix + "candidateJ_joint_analytic"),
                H("Joint analyticity of the regular J candidate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all Boolean e and f and complex u, v and r with "
                    + "‖u‖ + ‖r‖ < 1 and ‖v‖ + ‖r‖ < 1, the map "
                    + "p ↦ candidateJ(e,f,p.1,p.2,r) on ℂ × ℂ is complex analytic at (u,v). "
                    + "The original sources are analytic in their external coordinates, and the b factors "
                    + "and the normalized root sum give the required denominator bounds."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("candidates-original-joint-differentiable"),
                DeclarationHandle.Create(Prefix + "candidates_original_joint_differentiable"),
                H("Joint differentiability on the original source bidisk"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all Boolean e and f, complex u and v, and real 0 < r < 1 with "
                    + "‖u‖ + √r < 1 and ‖v‖ + √r < 1, both maps "
                    + "p ↦ candidateJ(e,f,p.1,p.2,(r : ℂ)) and "
                    + "p ↦ candidateT(e,f,p.1,p.2,(r : ℂ)) are jointly complex Fréchet differentiable "
                    + "at (u,v), in that order in the conjunction. The inequality r ≤ √r supplies the "
                    + "source disks for J. Nonvanishing of E gives joint analyticity of T there as well."))),
                DescribeRole.Theorem))));
}

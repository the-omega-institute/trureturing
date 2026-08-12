using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class CrossingNormFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The discriminant -3 crossing form represents exactly the Eisenstein norms, for every parameter.",
        H("The Crossing Form is the Eisenstein Norm Curve"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("crossing-form-range-equals-eisenstein-norm"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/CrossingNormForm.Qform_range_eq_eisNorm"),
                H("The crossing form represents exactly the Eisenstein norms for every t"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Q"), Underscore, F.Id("t"), Open, F.Id("P"), Comma, F.Id("Q"), Close, Sp, Eq, Sp,
                    F.Id("P"), Caret, Grp(D(2)), Minus,
                    Open, D(2), F.Id("t"), Plus, D(1), Close, F.Id("P"), F.Id("Q"), Plus,
                    Open, F.Id("t"), Caret, Grp(D(2)), Plus, F.Id("t"), Plus, D(1), Close,
                    F.Id("Q"), Caret, Grp(D(2)), Comma, Sp,
                    Operatorname, Grp(F.Id("disc")), Sp, Eq, Sp, Minus, D(3), RowBreak,
                    Operatorname, Grp(F.Id("range")), Sp, F.Id("Q"), Underscore, F.Id("t"), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("range")),
                    Open, F.Id("x"), Caret, Grp(D(2)), Plus, F.Id("x"), F.Id("y"), Plus, F.Id("y"), Caret, Grp(D(2)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The one-parameter crossing form Q_t(P,Q) = P^2 - (2t+1)PQ + (t^2+t+1)Q^2 has "
                        + "discriminant b^2 - 4ac = (2t+1)^2 - 4(t^2+t+1) = -3, identically in the parameter "
                        + "t, and reduces under the explicit unimodular substitution (P,Q) -> (P-(t+1)Q, Q) "
                        + "to the principal Eisenstein (Loeschian) norm form x^2 + xy + y^2. Consequently, "
                        + "for every integer t, the values represented by Q_t are exactly the Eisenstein "
                        + "norms: the whole one-parameter family collapses to the single value-set of the "
                        + "principal form.")),
                    Paragraph(Text(
                        "The reduction Q_t(P,Q) = eisNorm(P-(t+1)Q, Q) and the discriminant identity are "
                        + "ring identities. The value-set equality is both inclusions via the explicit "
                        + "unimodular change of variables and its inverse: the reduction gives range Q_t "
                        + "contained in range eisNorm, and eisNorm(x,y) = Q_t(x+(t+1)y, y) gives the reverse "
                        + "containment, so the two ranges coincide.")),
                    Paragraph(Text(
                        "Mathlib has no representation lemma for x^2 + xy + y^2 and no such parameterized-form "
                        + "reduction, so this is a genuine construction rather than a library restatement. It "
                        + "records the algebraic unified foundation of residual E.63 — the discriminant -3 "
                        + "identification of the crossing form with the Eisenstein norm curve. The criterion's "
                        + "crossing-if-and-only-if-continued-fraction-orbit biconditional, the three "
                        + "generation-mechanism laws, and the self-insertion ladder are not covered."))),
                DescribeRole.Theorem
            )),
        []));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryWholeGroupAbsoluteWidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One absolute positive length K=5 precedes every finite field, every natural rank, every nonidentity involutive field automorphism and every actual special-unitary target. Five ordered factors lie in the same determinant-one Hermitian special-unitary carrier and alternate U,L,U,L,U. Ranks0,1,2,3 and characteristic2 are retained. Genuine central-Levi reduction and absorption keep the length independent of rank and field size.",
        H("Unitary Whole Group Absolute Width"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitarywholegroupabsolutewidth-five-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWholeGroupAbsoluteWidth.five_factor"),
                H("five factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite field F, every natural rank n including 0,1,2,3, every nonidentity involutive field automorphism iota and every g in specialUnitary n iota, five_factor supplies FiveFactor g with no generation or factorization premise. FiveFactor gives a,b,c,d,e in that SAME determinant-one Hermitian SU, with Positive a, Negative b, Positive c, Negative d, Positive e and a*b*c*d*e=g. Thus choose the ONE positive absolute length K=5 BEFORE F,n,iota,g, and define f : Fin 5 -> specialUnitary n iota by f=![a,b,c,d,e] in that order. Positive means that ((f j).val.val-1) r c vanishes for c.val < r.val+1 at even j; Negative means it vanishes for r.val < c.val+1 at odd j. List.ofFn f is [a,b,c,d,e], and associativity gives its ordered product equal to g. This is the literal Fin 5/List-product formulation as a consequence of the fixed-five result, with the same field, rank, involution and target parameters; characteristic 2 and the small ranks are not excluded."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}

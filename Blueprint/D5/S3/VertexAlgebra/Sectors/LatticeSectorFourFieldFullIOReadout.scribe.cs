using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFourFieldFullIOReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorFourFieldFullIOReadout", H("Finite-target four-field outer collision readout"), Blocks(
            Describe.Lean(
                DescribeId.Create("latticesectorfourfieldfullioreadout-actual-four-field-fullio-middle-readout"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFullIOReadout.actual_four_field_fullIO_middle_readout"),
                H("Actual outer collision from the original middle numerator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Four labelled descendants u,v,t,q retain one original locality order k, all four truncations on w, all twenty-four product identities, both inner and middle collision identities, and the middle reconstruction from the same infinite numerator P. Fix the signed modes b,y of v on t and q on w. For any lawful FullIO F from alpha and (beta+gamma)+(eta+delta) to a finite sector object M, supported channel transport supplies clearing data N,A,B and a bivariate numerator Q on this fixed slice. At each explicit coordinate iota in Fin M.size, the cleared outer iterate (u_r(v_b t))_s(q_y w) equals an eight-index finite contraction of P[X0,X1+X2,X2,X3]. The outer collision index i ranges from zero through max(0,s-B+b+y+a1+a2+a3+3k); the remaining seven indices lie in the original middleFiber at [r-A-N+i,b,s-B-i,y]. The weight is the signed integer binomial coefficient with upper index N-r-1 times the original middleWeight; the incoming linear readout of F is applied to the original signed numerator coefficient. The middle fiber inequalities force every omitted term to vanish, including negative-target branches. N,A,B,Q are selected only after b,y; no bound uniform over varying fused states is required. The two-sided Gram inverse is used by the existing FullIO classification. Target charges may repeat, and the readout is linear rather than multiplicative. The canonical normalization and Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions remain those of the suppliers. This is a supported formal coefficient identity; it asserts no full pentagon, braided tensor category, analytic sewing or physical realization."))),
                DescribeRole.Theorem))));
}

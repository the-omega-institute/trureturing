using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathNegativeFloorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original negative defect is strictly greater than 23/50 on the whole closed Section 71 triangle.",
        H("Four-path negative full-triangle lower bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-path-section-71-segment-nonroot"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.segmentNonroot"),
                H("Section 71 non-radical segment bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The seven entries are fixed rational values indexed by Fin 7 and used as the non-radical bounds in the full-triangle proof."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-section-71-segment-radical"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.segmentRadical"),
                H("Section 71 radical segment bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The seven entries are fixed positive rational values indexed by Fin 7 and used as the radical bounds in the full-triangle proof."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-section-71-segment-majorants-lt-floor"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.segment_majorants_lt_floor"),
                H("Finite segment majorants below the common floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every i : Fin 7, the corresponding rational non-radical and radical entries sum to a value strictly below 49359/40000. The proof enumerates Fin 7 and closes the seven rational inequalities.")),
                    Paragraph(Text("The finite comparison is consumed by negative_floor when the actual closed-triangle support bounds are split into the seven cases; it makes no independent assertion about the defect."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-h"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.h"),
                H("The constant h"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("h=1/sqrt(2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-c"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.c"),
                H("The constant c"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("c=cos(pi/8)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-s"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.s"),
                H("The constant s"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("s=sin(pi/8)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-l"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.L"),
                H("The trace threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real q, L(q)=19/16+q/2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-r"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.R"),
                H("The fixed negative-row R radical"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real q,X,Y, R(q,X,Y)=sqrt(s²X+h²Y+sh(L(q)²−X−Y)). The order of X and Y is the negative row of Definition 57.1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-c-radical"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.C"),
                H("The fixed negative-row C radical"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real q,X,Y, C(q,X,Y)=sqrt(c²(1−X)+h²(1−Y)+2chF(L(q),X,Y)). F retains the original normalized Z radical."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-gamma"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.Gamma"),
                H("The shared-feedback response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real q,X,Y, Gamma(q,X,Y)=sqrt(1−q) R(q,X,Y)+sqrt(q) C(q,X,Y). Both terms use the same X,Y and the same original fibre radical."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-e"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.E"),
                H("The negative-row energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real q, E(q)=(2(h+s))²(1−q)+(2(h+c))²q. These are the original e² and d² coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-g"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.G"),
                H("The original negative defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real q,X,Y, G(q,X,Y)=E(q)−4Gamma(q,X,Y)². This is the negative row G_- of Definition 57.1, with all square roots on their nonnegative branches."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-negative-floor-negative-floor"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNegativeFloor.negative_floor"),
                H("The full Continuation VI Theorem 71.1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real q in [11/100,23/200] and every real X,Y in [0,1] with sqrt(X)+sqrt(Y)≥19/16+q/2, G(q,X,Y)>23/50. All triangle edges and degenerate fibres remain in scope. The estimate is a strict real lower bound. The proof preserves the fixed labels: it bounds the linear term in Y−X directly, without swapping the original inputs. Young’s inequality bounds Gamma² by alpha R²+beta C² for alpha=1−q+(13/10)sqrt((1−q)q) and beta=q+(10/13)sqrt((1−q)q). The original radical identities and the closed triangle ball inequality give a support term bounded by sqrt((185961/1250000)T). The seven rational comparisons are consumed after splitting the interval [1,11/10] at 21/20. On [1,21/20], T≤539/625; on [21/20,11/10], T≤361/400 and the radical bound 367/1000 combines with the nonradical bound at 21/20. This yields Gamma²<49359/40000. The independently derived strict energy inequality 49359/40000<(E(q)−23/50)/4 then gives the result. This is an application of the repository’s original scalar defect model; no physical realization or literature novelty is asserted."))),
                DescribeRole.Theorem))));
}

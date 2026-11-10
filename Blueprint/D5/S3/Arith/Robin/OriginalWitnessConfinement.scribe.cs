using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalWitnessConfinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive actual witnesses give attained complete prime-label windows and all-tie confinement.",
        H("Original Witness Confinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-window-positive-witness"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/OriginalWitnessConfinement.original_window_of_positive_witness"),
                H("Full infinite-domain attainment from a positive witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The ordinary source geometry is FW0-FW2 and N1 in "
                        + "Library/ArithSums/nicolas2025comparison.md. This "
                        + "formal argument uses the weaker compiled unconditional "
                        + "Gronwall/Mertens envelope, not the stronger Robin "
                        + "estimate quoted there. Write F(n)=log(sigma(n)/n) "
                        + "minus log(log(log(n))), and gamma for Euler's constant.")),
                    Paragraph(Text(
                        "Let m be an actual natural integer, log(m)>1, delta>0, "
                        + "and F(m)>=gamma+delta. Assume the explicit padding "
                        + "budget (log(5040)+2*ell)/(log(m)*log(log(m)))<=delta/2. "
                        + "Put R=exp(39/(5*delta)); assume 286<=R and "
                        + "2*R<exp(ell). The theorem constructs an OriginalWindow "
                        + "whose labelStart is ell and whose labels are literally "
                        + "originalLabelWindow(ell), including both prime endpoints. "
                        + "It requires no nonempty label or selected-domain premise.")),
                    Paragraph(Text(
                        "At A=log(n)>=286, sigma_split and the effective Mertens "
                        + "product estimate give sigma(n)/n<=exp(gamma)*log(A)*"
                        + "exp(39/(10*log(A))). The two error contributions are "
                        + "2/log(A) and 19/(10*log(A)). Taking logarithms yields "
                        + "F(n)-gamma<=39/(10*log(A)). Hence A>R forces "
                        + "F(n)<gamma+delta/2. The exclusion is strictly beyond R; "
                        + "the clock endpoint A=R remains included.")),
                    Paragraph(Text(
                        "For every label p, form L=lcm(5040,m), D=p*L. "
                        + "Then m divides D and 5040*p divides D, even when "
                        + "p already divides L. Divisibility monotonicity of "
                        + "abundancy and log-log tangency at log(m) bound the "
                        + "objective loss by (log(5040)+log(p))/(log(m)*log(log(m))). "
                        + "Thus F(D)>=gamma+delta/2, and the strict tail implies "
                        + "log(D)<=R. No absent-prime or GA2 condition is used.")),
                    Paragraph(Text(
                        "The finite set consists of all integers in the closed "
                        + "interval from 1 through floor(exp(R)) that are divisible "
                        + "by 5040*p. It contains D. A finite maximum compares "
                        + "every member, while every legal integer outside it has "
                        + "objective strictly below F(D). This proves maximality "
                        + "over the entire infinite class of positive 5040*p "
                        + "multiples. Every maximizing tie compares against D, "
                        + "so every tie has F(N)>=gamma+delta/2 and log(N)<=R. "
                        + "Legality and exp(ell)<=p give ell<=log(N).")),
                    Paragraph(Text(
                        "Applying the all-tie bounds to the least canonical "
                        + "sources proves literal OriginalBounds. Strict label "
                        + "separation gives both endpoint inequalities 2*R<p,r "
                        + "on every original good edge without any source-order "
                        + "hypothesis. Empty windows and empty good-edge sets "
                        + "remain valid. The definitions of the objective, full "
                        + "maximality, original label interval and selectedDomain "
                        + "are unchanged.")),
                    Paragraph(Text(
                        "This conditional construction neither supplies the "
                        + "positive integer witness from RH failure nor proves "
                        + "cofinality, good-edge existence, positive selected mass, "
                        + "signed endpoint or late-row estimates, normalizer "
                        + "transfer, a favorable signed prime moment, or RH."))),
                DescribeRole.Theorem))));
}

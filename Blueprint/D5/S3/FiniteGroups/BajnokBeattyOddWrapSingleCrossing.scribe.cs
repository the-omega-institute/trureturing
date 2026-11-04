using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyOddWrapSingleCrossingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite normalized binomial recurrence proves a unique sign threshold for the original odd-wrap quotient return counts.",
        H("The unique odd-wrap sign threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-single-crossing"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapSingleCrossing.actual_odd_wrap_single_crossing"),
                H("A nonnegative odd-wrap defect is followed only by strictly positive defects"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every odd integer p>=3 and every natural t>=2 put m=6t-1 and L=p*m. The original_return_pair definition retains the complete original quotient maps: K19 is the integer span of (p(m-1)/2,p(m+1)/2) and (p(m-9)/2,-p(m+9)/2); K33 is the integer span of (p(m-3)/2,p(m+3)/2) and (p(m-3)/2,-p(m+3)/2). Its components are W19 and W33 at length L.toNat. Composite odd p remain in scope.")),
                    Paragraph(Text("There is exactly one natural T>2 such that W33<W19 for every 2<=t<T, W19<=W33 at t=T, and W19<W33 for every t>T. Consequently equality can occur at most once, at the threshold. The theorem permits a strict jump across zero and does not assert that an equality point exists. This is a theorem about the original signed coordinate-word return counts, not a claim about an arbitrary graph spectrum or an asymptotic approximation.")),
                    Paragraph(Text("Write p=2u+1 and K(m,j)=choose(2m+1,m-j). The three columns have j=u,3u+1,9u+4. Starting at m=9u+4, every denominator and binomial coefficient is positive. With lambda(j)=j(j+1), S(m)=(m+1)(m+2), a=2p^2, q=S(m)-lambda(u), X=K(m,3u+1)/K(m,u) and Y=K(m,9u+4)/K(m,u), the existing choose_two_step_rat supplier gives X'=X*q/(q-a) and Y'=Y*q/(q-10a). The lambda gaps are exactly a and 10a.")),
                    Paragraph(Text("The normalized defect d=2X-1-Y satisfies d'-d=(X'-X)(2-10Y'/X'), with X'-X>0 and Y/X strictly increasing. Thus the step slopes strictly increase. If the slope at b is below 2, every earlier step up to b increases d; if it is at least 2, every step after b is nonincreasing. In the latter case the already proved late positive cone supplies an arbitrarily distant actual sample with positive d, forcing d(b)>0. This proves that d(a)>=0 implies d(b)>0 for every a<b, using finite recurrence arguments only.")),
                    Paragraph(Text("The actual sample is m=9u+4+p(3t-5). Binomial symmetry and actual_odd_wrap_counts identify the original count difference exactly as W33-W19=2K(m,u)(2X-1-Y). The positive factor transfers sign persistence to the quotient counts. The earlier initial-sign theorem gives W33<W19 at t=2, while actual_late_odd_wrap_sign gives positive samples arbitrarily far out. The least nonnegative sample is the threshold, and sign persistence proves both strict positivity afterward and uniqueness."))),
                DescribeRole.Theorem))));
}

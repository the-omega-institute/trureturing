using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalPureCompactnessDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    public DocumentDefinition Create()
    {
        Formula r = Seq(Mathbb, Grp(V("R"))), v = V("V"), c = V("C"), u = V("u"), x = V("x");
        Formula strict = All("x", v, Imp(Seq(x, InMacro, Sp, c),
            Imp(Seq(x, Neq, Sp, D(0)), Seq(D(0), F.Lt, Sp, C("apply", u, x)))));
        Formula statement = All("V", V("Type"), Seq(
            OpenBracket, C("NormedAddCommGroup", v), CloseBracket, Sp,
            OpenBracket, C("NormedSpace", r, v), CloseBracket, Sp,
            OpenBracket, C("FiniteDimensional", r, v), CloseBracket, Sp,
            OpenBracket, C("Nontrivial", v), CloseBracket, Sp,
            All("C", C("PointedCone", r, v), All("u", C("LinearMap", r, v, r),
                Imp(C("IsClosed", c), Imp(strict, Imp(Eq(C("span", r, c), C("top")),
                    Imp(C("exclusionBalls", c, u), Imp(C("weakPair", c, u),
                        C("IsCompact", C("pure", c, u)))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The entire extreme-point locus of the original normalized cone base is compact under complete exclusion balls and weak orthogonal-pair properness.",
            H("Compactness of the original pure locus"), Blocks(
                Describe.Lean(DescribeId.Create("whole-pure-compact"),
                    DeclarationHandle.Create("D5/S3/Quantum/Foundation/OriginalPureCompactness.whole_pure_compact"),
                    H("Original pure-point compactness"), StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Let V be a nonzero finite dimensional real normed vector space, C a closed generating pointed cone, and u a real linear functional strictly positive on every nonzero point of C. The normalized base K is the entire intersection of C with u=1. Its pure locus P consists of all extreme points. Effects range over every original linear functional between zero and u on all of C. Each complete original exclusion fibre is a nondegenerate affine Euclidean ball, and every original orthogonal pure pair generates a proper face. Then P is compact in V. No closedness or finiteness of P is assumed.")),
                        Paragraph(Text("The full effect interval is closed. Choose a finite basis from the spanning original pure locus. Every proper effect has values between zero and one on this basis, so the basis operator-norm estimate bounds the entire interval. Finite dimensionality makes that closed bounded interval compact.")),
                        Paragraph(Text("Joint completion makes the map sending a pure point to its entire exclusion ball injective: complete one point to a joint triple; the other two points have a singleton common exclusion. Two exclusion balls containing two different states are equal, since their intersection is a nonpoint face of each strictly convex ball.")),
                        Paragraph(Text("Suppose an original effect a confirms x and vanishes at y and z, while another original effect distinguishes y and z. The face where a=1 contains x. If this face were a nonpoint ball, take two antipodal extreme points s and t in it. The same a would put both y and z into both complete exclusion balls D_s and D_t. These balls must coincide, and injectivity forces s=t, contradicting their antipodality. The confirming face is therefore a pure singleton, and x is pure.")),
                        Paragraph(Text("Consider all triples x,y,z in K and all pairs of original effects a,b satisfying a(x)=1, a(y)=a(z)=0, b(y)=1 and b(z)=0. This is a closed subset of a compact product. Its projection onto x is contained in P by the preceding argument. Conversely every original pure point has such a configuration by joint completion and the common confirming effects of complete exclusion balls. Thus this projection equals the entire P and is compact.")),
                        Paragraph(Text("This supplies closedness of the original pure locus for limits of complete exclusion balls. It does not itself establish uniform semiaxis bounds, continuity of the complete balls, or local triviality of their direction spaces."))), DescribeRole.Theorem))));
    }
}

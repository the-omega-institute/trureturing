using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;
internal sealed class TypedCocycleSharpNativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact static and complete names-only online minima for the fixed native two-channel source.",
        H("Sharp whole-source native law"),
        Blocks(Describe.Lean(DescribeId.Create("whole-sharp-native-law"),
            DeclarationHandle.Create("D5/S3/Observer/Completion/TypedCocycleSharpNative.whole_sharp_native_law"),
            H("Both attained minima and all closed thresholds"), StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("For h>0, epsilon>0 and fixed C,E, quantum is floor(2epsilon/h)+1. LeastCost means an attained cost together with a lower bound for every feasible competing cost. Feasible requires one decoder returning the entire original ordered word for every point of the full closed coordinate box, from exactly its endpoint, final supplement and joint vector. Negative observations near the empty word are retained. Neither definition mentions quantum or the asserted optimum.")),
                Paragraph(Text("Static labels are arbitrary functions on the infinite whole legal-history domain with finite actual range, without prefix compatibility. Online registers have a single initialization and a total update on names alone. Their cost is the complete actual reached range over all legal histories at p,s,t together. The reached range is never assumed closed under source-illegal names. Every persistent variable belongs to the charged state.")),
                Paragraph(Text("The lower bound uses actual s histories with counts m=k+2i-j and n=k+j-i, for 0<=i,j<=k. Their native coordinates are C+h(2k+i,3k+j). A single observation C+h(2k+k/2,3k+k/2) belongs to all their original closed boxes whenever hk<=2epsilon. Decoder correctness injects this square into any actual label range. Every online register induces such a static label. Appending e translates the square by E at t.")),
                Paragraph(Text("For attainment, the entire state is (x,y) in (Z/qZ)^2, initialized at (0,0). The single a update is (x+1,y), c is (0,x), and e is the identity. The register values are (m,0) at p and (n,m) at s,t. Every pair is reached at s with nonnegative representatives, so the complete range has q squared states. Equal endpoint and equal residues, together with a common allowed observation, force both integer native coordinates equal; the inverse integer matrix then forces both original counts equal.")),
                Paragraph(Text("The decoder is a mathematical factorization of compatible explanations through the permitted final input. Mathlib Function.factorsThrough_iff supplies this factorization after uniqueness is proved. Mathlib modular equality, integer divisibility bounds, and finite-cardinality injections supply the generic algebra and counting. This is not an effective representation claim for unspecified real constants.")),
                Paragraph(Text("Both exact minima equal q squared for every positive h,epsilon. The constant-label contract holds exactly when h>2epsilon. For every k>=0 with kh<=2epsilon<(k+1)h, quantum=k+1, hence both minima are (k+1) squared. The left endpoint is closed, including positive equality thresholds; k=0 retains epsilon>0 and q=1. All original empty, zero-lap, intermediate and terminal uses share this same update and decoder.")),
                Paragraph(Text("The parameterized result concerns the fixed native instrument A=h(1,1), B=h(1,2), without retuning edge vectors. C,E may be arbitrary real offsets in the theorem, which includes the source positive case. It asserts no result for other source propositions, other native matrices, scalar acquisition, physical instruments, finite clock range or total chronological storage."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Seq(Operatorname, Grp(F.Id(name)))
            : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula All(Formula variables, Formula type, Formula body) =>
        Seq(Forall, Sp, variables, Colon, Sp, type, Comma, Sp, body);

    private static Formula Same(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);

    private static Formula Both(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Land, Sp, Open, right, Close);

    private static Formula TheoremFormula()
    {
        Formula h = F.Id("h"), epsilon = F.Id("epsilon");
        Formula c = F.Id("C"), e = F.Id("E"), k = F.Id("k");
        Formula quantum = Call("quantum", h, epsilon);
        Formula square = Seq(quantum, Caret, Grp(D(2)));
        Formula twice = Seq(D(2), Sp, epsilon);
        Formula assumptions = Both(Seq(D(0), Sp, Lt, Sp, h),
            Seq(D(0), Sp, Lt, Sp, epsilon));
        Formula staticMinimum = Call("LeastCost", Call("StaticCost", h, epsilon, c, e), square);
        Formula onlineMinimum = Call("LeastCost", Call("OnlineCost", h, epsilon, c, e), square);
        Formula constant = Call("const", Call("History"), Seq(Open, Close));
        Formula supplement = Seq(Call("Feasible", h, epsilon, c, e, constant),
            Sp, Iff, Sp, twice, Sp, Lt, Sp, h);
        Formula next = Seq(Open, k, Sp, Plus, Sp, D(1), Close);
        Formula thresholds = All(k, Seq(Mathbb, Grp(F.Id("N"))),
            Seq(k, Sp, h, Sp, Le, Sp, twice, Sp, Rightarrow, Sp,
                twice, Sp, Lt, Sp, next, Sp, h, Sp, Rightarrow, Sp,
                Same(quantum, Seq(k, Sp, Plus, Sp, D(1)))));
        return Disp(All(Seq(h, Comma, Sp, epsilon), Seq(Mathbb, Grp(F.Id("R"))),
            All(Seq(c, Comma, Sp, e), Call("Vector"),
                Seq(Open, assumptions, Close, Sp, Rightarrow, Sp,
                    Both(staticMinimum, Both(onlineMinimum, Both(supplement, thresholds)))))));
    }
}

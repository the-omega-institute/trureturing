using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBIdempotentSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unchanged original directed positive two-table gives the exact norm-product cone bounds and closure of its total response in every actual original idempotent corner.",
        H("Original two-table idempotent support"),
        Blocks(
            Paragraph(Text("Let X be an arbitrary complete real normed vector space with the six-law JB data (S,u). Let E be any original real normed label space, J its real bilinear Jordan product, i:E->X a real linear isometry satisfying i(J(a,b))=S(i(a),i(b)), C its exact ambient square cone, and P the unchanged type of original evaluation labels. Thus e belongs to C exactly when i(e) is an actual square in X, and exactly when every original real linear evaluation alpha reads e nonnegatively. Let D:E x E->E be any total map. The table has diagonal alpha(J(a,a)), alpha(J(b,b)), upper entry alpha(J(a,b))-i alpha(D(a,b)), and lower entry alpha(J(b,a))-i alpha(D(b,a)); require this actual directed complex table positive semidefinite for every original alpha,a,b.")),
            Describe.Lean(DescribeId.Create("original-two-table-corner-support"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBIdempotentSupport.original_p2_support"),
                H("Quantitative support in the original corner"),
                StatementSource.FromAuthor(F.Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any actual original p with J(p,p)=p, write E(p)={a in E:S(i(p),i(a))=i(a)}. For all a,b in E(p), set c=norm(a)norm(b). The conclusions are cp+D(a,b) in C, cp-D(a,b) in C, and D(a,b) in E(p). The norm is the unchanged original norm, and the corner is literally the inverse image of the ambient Peirce two-space. Density, a unit in E and separation may additionally be supplied as in the original setting; the proof establishes this conclusion without needing those extra hypotheses. In particular it applies to the original dense unital faithful Jordan subalgebra without changing its carrier.")),
                    Paragraph(Text("The ambient square bound gives 0<=alpha(J(a,a))<=norm(a)^2 alpha(p), and the analogous bound for b. The existing original positive-table transfer theorem gives alpha(D(a,b))^2<=alpha(J(a,a))alpha(J(b,b))-alpha(J(a,b))^2. Since alpha(p)>=0, scalar comparison gives abs(alpha(D(a,b)))<=c alpha(p). Exact detection by the same original evaluations puts cp+D(a,b) and cp-D(a,b) in C. The ambient support theorem then gives S(i(p),i(D(a,b)))=i(D(a,b)). Every square root used here belongs to X; D is called only on the original a,b in E.")),
                    Paragraph(Text("In the original unital setting, let e in E be the original unit, with i(e)=u. All original evaluation labels are retained. Their masses alpha(e) may be zero, unequal or subnormalized; no mass is divided out and no additional preparation is introduced. There is no additivity, homogeneity, continuity, NN or Jacobi hypothesis on D. The conclusion includes zero X, p=0, p=e, zero masses and zero inputs. This result supplies the ambient support step for a separately established quotient bound, but proves neither an actual quotient response interface nor the positivity of a proposed quotient-corner readout, nor general response descent or physical reconstruction.")))))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(V(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Image(Formula x) => Call("i", x);
    private static Formula Product(Formula x, Formula y) => Call("S", x, y);
    private static Formula Supported(Formula x) => Eq(Product(Image(V("p")), Image(x)), Image(x));
    private static Formula Mem(Formula x) => Call("mem", x, V("C"));
    private static Formula CP => Call("scale", Call("multiply", Call("norm", V("a")), Call("norm", V("b"))), V("p"));
    private static Formula Response => Call("D", V("a"), V("b"));
    private static Formula Statement()
    {
        Formula body = All("p", V("E"), All("a", V("E"), All("b", V("E"),
            Imp(And(Eq(Call("J", V("p"), V("p")), V("p")), And(Supported(V("a")), Supported(V("b")))),
                And(Mem(Add(CP, Response)), And(Mem(Sub(CP, Response)), Supported(Response)))))));
        body = Imp(Call("OriginalTwoTableHypotheses", V("X"), V("S"), V("u"), V("E"), V("J"), V("D"), V("C"), V("i"), V("P"), V("evaluation")), body);
        body = All("evaluation", Call("EvaluationFamilies", V("P"), V("E")), body);
        body = All("i", Call("RealLinearIsometries", V("E"), V("X")), body);
        body = All("C", Call("Sets", V("E")), body);
        body = All("D", Call("TotalBinaryMaps", V("E")), body);
        body = All("J", Call("RealBilinearMaps", V("E")), body);
        body = All("E", V("RealNormedSpaces"), All("P", V("Types"), body));
        body = All("u", V("X"), body);
        body = All("S", Call("RealBilinearMaps", V("X")), body);
        return All("X", V("CompleteRealNormedSpaces"), body);
    }
}

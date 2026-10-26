using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WormaldTournamentHessian;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular tournament Hessians: result.",
        H("Tournament Hessian: result"), Blocks(
            HessianResolution())));

    private const string Prefix = "D5/S3/Combinatorics/WormaldTournamentHessian/Result.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/wormald2026tournaments");

    private static Formula SourceH => Seq(Mathcal, Sp, Grp(V("H")));

    private static DocumentBlock Helper(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("wormald-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Skew => Call("Matrix.map", Call("skewAdjacency", V("A")), Call("Int.castRingHom", C));

    private static Formula V(string name) => F.Id(name);

    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));

    private static Formula C => Seq(Mathbb, Sp, Grp(V("C")));

    private static Formula Q => Seq(Mathbb, Sp, Grp(V("Q")));

    private static Formula Index => Call("Fin", V("d"));

    private static Formula ShortIndex => Call("Fin", Call("Nat.sub", V("d"), D(1)));

    private static Formula ShortVector => new Formula.TypeArrow(ShortIndex, C);

    private static Formula HType => new Formula.TypeArrow(ShortVector, C);

    private static Formula AType => new Formula.TypeArrow(Index, new Formula.TypeArrow(Index, V("Bool")));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula WithA(Formula body) => All("d", N, All("A", AType, body));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(word));
        }
        var head = Seq(Operatorname, Sp, Grp([.. parts]));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }

    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);

    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));

    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Smul(Formula a, Formula b) => Seq(a, Cdot, Sp, Parenthesized(b));

    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);

    private static Formula ClaimFormula() => All("d", N, Imp(Le(D(3), V("d")), All("A", AType,
        Imp(Call("IsRegularTournament", V("A")), And(Ex("h", HType, Call("IsLocalSolution", V("A"), V("h"))),
            All("h", HType, Imp(Call("IsLocalSolution", V("A"), V("h")),
                And(Ne(Call("calH", V("h")), D(0)), Ex("q", Q,
                    Eqn(Fr(V("d"), Call("calH", V("h"))), new Formula.Power(Call("Rat.cast", V("q")), D(2))))))))))));

    private static DocumentBlock HessianResolution() => new DocumentBlock.Section(
        H("The Hessian closed form and rational square"), Blocks(
            Paragraph(Text("§1, Conjecture 6: “For every regular tournament "),
                    Math(new Formula.Power(V("T"), Star)), Text(" on at least three vertices, "),
                    Math(Ne(SourceH, D(0))), Text(" and "), Math(Fr(V("d"), SourceH)),
                    Text(" is the square of a rational.”")),
            Helper("calH_closedForm", "The closed form for the analytic Hessian determinant",
                HessianClosedFormFormula(),
                "For every regular tournament of order d at least three and every complex C2 local solution h, the actual real angular Hessian determinant is d times det(d²I+S²) divided by det(d²I−S²). The Hessian is defined by two real Frechet derivatives of the logarithmic phase."),
            Describe.Lean(DescribeId.Create("wormald-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The rational-square conjecture"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Write C=½I+A and let J have every entry equal to one. Tournament completeness gives 2C=J+S. For nonzero coordinates y and nonsingular Q(y)=diag(2/y)−S, the matrix determinant lemma factors K(y) as det Q(y), the product of the coordinates y_j/2, and one minus the sum of all entries of Q(y) inverse. Call that inverse-entry sum alpha. At the constant point z=2/d, the resolvent is dI−S. Strict diagonal dominance makes it nonsingular, and regularity gives row and column sums 1/d for its inverse.")),
                    Paragraph(Text("The resolvent inverse and alpha are complex C2 near the constant point. Every first coordinate derivative of alpha there is 1/2. Its second derivative in coordinates j and k is z to the power minus two times V_jk+V_kj, minus z inverse when j=k, where V=(dI−S) inverse. The equation alpha(y,h(y))=1 holds on a neighbourhood for every local solution. Its first derivative gives each coordinate derivative of h equal to minus one; its second derivative gives the corresponding difference of four alpha second derivatives.")),
                    Paragraph(Text("The exponential coordinate chart and the principal logarithm are C2 at the base point because h takes the positive value z there. Applying the second Frechet chain rule and then substituting imaginary angular coordinates identifies the actual angular Hessian with minus R transpose T R. Here the columns of R are e_j−e_d and T=I−d(V+V transpose). Both row and column sums of T are minus one. The matrix whose columns are R followed by the all-ones vector has determinant d; conjugating T by this matrix gives diagonal blocks R transpose T R and minus d. Consequently det(R transpose T R)=−d det T.")),
                    Paragraph(Text("The resolvent identity gives T=−(d²I+S²)(d²I−S²) inverse. All required inverses follow from the nonzero shifted determinants. The order d is odd, so its determinant contributes one minus sign, while the angular Hessian has the even size d−1 and its overall minus sign does not change its determinant. This proves the displayed closed form for calH.")),
                    Paragraph(Text("Transposition identifies det(dI−S) with det(dI+S). Factoring the quadratic matrices therefore makes det(d²I−S²) the square of an integer. In odd dimension, det(S+idI) is a purely imaginary Gaussian integer; dividing it by i gives a nonzero integer, and det(d²I+S²) is its square. The quotient of these two quadratic determinants is thus the square of a nonzero rational. The closed form identifies this quotient with d divided by calH, and also gives nonvanishing of calH.")),
                    Paragraph(Text("Finally, every first coordinate derivative of K at the constant point equals −det(dI−S)/(2d^d), which is nonzero. The complex implicit function theorem supplies a C2 local solution with value z and the required equation germ. Together with the Hessian calculation for every such solution, this proves both clauses of the conjecture."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wormald-2026-tournament-hessian-square"),
                    ResolutionKind.Proved))));

    private static Formula HessianQuadraticPlus => Call("Matrix.det",
        Add(Smul(new Formula.Power(Call("Nat.cast", V("d")), D(2)), D(1)), Mul(Skew, Skew)));

    private static Formula HessianQuadraticMinus => Call("Matrix.det",
        Sub(Smul(new Formula.Power(Call("Nat.cast", V("d")), D(2)), D(1)), Mul(Skew, Skew)));

    private static Formula HessianClosedFormFormula() => WithA(Imp(Le(D(3), V("d")),
        Imp(Call("IsRegularTournament", V("A")), All("h", HType,
            Imp(Call("IsLocalSolution", V("A"), V("h")),
                Eqn(Call("calH", V("h")),
                    Fr(Mul(Call("Nat.cast", V("d")), HessianQuadraticPlus), HessianQuadraticMinus)))))));

}

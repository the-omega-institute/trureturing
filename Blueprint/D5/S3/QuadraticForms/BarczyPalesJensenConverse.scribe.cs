using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class BarczyPalesJensenConverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/BarczyPalesJensenConverse.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/barczypales2025jensen");
    private static Formula X(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Inverse(Formula value) => new Formula.Power(Parenthesized(value), new Formula.Negate(D(1)));
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Op("fun"), Sp, Parenthesized(Seq(X(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, body);
    private static Formula Real => Seq(Mathbb, Grp(X("R")));
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Claim => Op("claim");
    private static Formula FinN => C("Fin", X("n"));

    private static Formula Method(Formula receiver, string name) => Seq(receiver, Dot, X(name));

    private static Formula SubtypeValue(Formula value, Formula membership) =>
        Seq(Langle, value, Comma, Sp, membership, Rangle);

    private static Formula IntervalMean(Formula hI, Formula n, Formula x) =>
        SubtypeValue(
            SumOver("j", C("Fin", n),
                Mul(Inverse(Typed(n, Real)), Typed(App(x, X("j")), Real))),
            Method(hI, "sum_mem"));

    private static Formula IntervalRow(Formula hI, Formula p, Formula x, Formula i) =>
        SubtypeValue(
            SumOver("j", C("Fin", X("n")),
                Mul(App(App(p, i), X("j")), Typed(App(x, X("j")), Real))),
            Method(hI, "sum_mem"));

    private static Formula Vector2(Formula u, Formula v) =>
        Seq(Bang, OpenBracket, u, Comma, Sp, v, CloseBracket);

    private static Formula WholeClaim
    {
        get
        {
            var f = X("f"); var p = X("P"); var x = X("x"); var interval = X("I");
            var hI = X("hI");
            var hypothesis = All("x", new Formula.TypeArrow(FinN, interval),
                Le(App(f, IntervalMean(hI, X("n"), x)),
                    Fr(SumOver("i", FinN, App(f, IntervalRow(hI, p, x, X("i")))), X("n"))));
            var midpoint = All("u", interval, All("v", interval,
                Le(App(f, IntervalMean(hI, D(2), Vector2(X("u"), X("v")))),
                    Fr(Add(App(f, X("u")), App(f, X("v"))), D(2)))));
            var body = Imp(hypothesis, midpoint);
            body = Imp(Le(D(2), C("rank", p)), body);
            body = All("hP", new Formula.Relation(p, FormulaRelationOperator.MemberOf,
                C("doublyStochastic", Real, FinN)), body);
            body = All("P", C("Matrix", FinN, FinN, Real), body);
            body = All("f", new Formula.TypeArrow(interval, Real), body);
            body = All("hI", C("Convex", Real, interval), body);
            body = Imp(C("IsOpen", interval), body);
            body = Imp(C("Nonempty", interval), body);
            body = All("I", C("Set", Real), body);
            return All("n", Nat, Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, X("n")), body));
        }
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A signed quadratic norm gives an all-input counterexample to the unrestricted rank-only Jensen converse.",
        H("A quadratic-field counterexample to the rank-only Jensen converse"), Blocks(
            Paragraph(Text("The source is Barczy and Pales, Jensen convex functions and doubly stochastic matrices, arXiv:2510.03715v1, Remark 2.2(i), referring to Theorem 2.1(i), equation (2.1), and Definition 1.1. Jensen convexity there means midpoint convexity. The question replaces the theorem's special column-span condition by real rank at least two. It imposes no continuity, measurability, boundedness, rational-entry condition or extra column-span assumption.")),
            Paragraph(Text("In the formula, Fin(n) is the finite type with n coordinates and I in a function type is the original interval subtype. Every arithmetic mean is the displayed subtype constructor ⟨∑(j : Fin n), (n : ℝ)⁻¹ * (x j : ℝ), hI.sum_mem⟩, with weights proved nonnegative from n > 0, total weight proved one using that same hypothesis, and each x j membership supplied by (x j).property. Every matrix row is the displayed subtype constructor ⟨∑(j : Fin n), P i j * (x j : ℝ), hI.sum_mem⟩, whose weight hypotheses are the nonnegativity and row-sum components of hP. The casts are the subtype values (x j : ℝ), so the formula uses the actual mean and row outputs in I rather than display abbreviations. The native doublyStochastic set requires every entry to be nonnegative and every row and column sum to be one.")),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The complete original universal converse"), StatementSource.FromAuthor(Disp(Eq(Claim, WholeClaim))),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("For every positive integer n, every nonempty open convex subset I of the real line, every arbitrary function f from I itself to the reals, and every real n by n doubly stochastic matrix P of real rank at least two, the inequality f applied to the displayed subtype arithmetic mean is at most the average of f applied to the displayed subtype matrix rows for every x in I^n is asserted to imply midpoint convexity for every u and v in I. Nonempty open convex subsets of the real line are exactly the open intervals in scope, including unbounded intervals and the whole line. The antecedent compares the actual arithmetic-mean input with the actual matrix row images for all inputs. The claim is a closed proposition and contains no restriction of arbitrary subtype functions to functions supplied with an ambient extension."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Negation of the complete converse"), StatementSource.FromAuthor(Disp(new Formula.Not(Claim))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("The entire universal claim is false: there exist a positive dimension, a nonempty open real interval, an actual function on that interval and an actual real doubly stochastic matrix of rank at least two for which the comparison holds at every input but midpoint convexity fails. The witness uses n=3 and I equal to the whole real line. The source definition and the result have literal types Prop and Not claim, respectively.")),
                    Paragraph(Text("Let s=sqrt(3). The implemented field K is QuadraticAlgebra Q 3 0, with omega=(0,1) and omega^2=3. The rational nonsquare fact follows from the existing prime nonsquare theorem. QuadraticAlgebra.lift sends a+b*omega to a+b*s in the reals. Its field homomorphism is injective, identifying K with the actual embedded field Q(s). The real K-algebra and scalar module are induced by this embedding. Applying the existing vector-space linear splitting to the injective K-linear embedding gives a total K-linear left inverse L from all real numbers to K, fixing every embedded field element. This is an actual classical-choice construction; no retraction, scalar certificate or regularity hypothesis is added.")),
                    Paragraph(Text("Define F(x) to be the rational-to-real cast of N(L(x)), where N(a+b*omega)=a^2-3*b^2 is the signed quadratic norm. L need only be K-linear; its multiplicativity is never asserted. On I=univ the witness subtype function sends an interval element x to F(x.val). All interval membership proofs are supplied by the convex-combination constructors.")),
                    Paragraph(Text("The actual matrix is P=(1/12)*[[5,3,4],[s+2,6-s,4],[5-s,3+s,4]]. The bounds 1<s<2 prove nonnegative entries, and each row and column sums to one. The top-left two by two minor has determinant (3-s)/18, which is positive. The existing determinant-rank and submatrix-rank theorems therefore give real rank at least two for this same matrix.")),
                    Paragraph(Text("For an arbitrary real triple x, set m=(x(0)+x(1)+x(2))/3 and t=(x(0)-x(1))/12. Direct matrix multiplication gives Px=(m+t,m+(s-2)*t,m+(1-s)*t). K-linearity of L transports these three entries to A+B, A+(omega-2)*B and A+(1-omega)*B, with A=L(m) and B=L(t). For all A,B in K, direct expansion of the quadratic norm gives N(A+B)+N(A+(omega-2)*B)+N(A+(1-omega)*B)=3*N(A). After rational casting this proves sum_i F((Px)(i))=3*F(m) for every real input. There is no division by input-dependent quantities, rational-input restriction or finite-sample substitution. The source inequality holds with equality at every legal input.")),
                    Paragraph(Text("Retraction fixes s and -s, so F(s)=F(-s)=-3 and F(0)=0. Applying the alleged midpoint conclusion to the two interval elements s and -s would require 0<=-3. The contradiction uses the complete universal converse through its legal n=3 witness; it does not merely negate a witness-only surrogate.")),
                    Paragraph(Text("This mathematical result concerns the exact unrestricted v1 question. The paper's positive theorem under its original column-span hypothesis and its forward Jensen-convexity implications are not contradicted. Regularity-restricted variants are separate questions. The bounded literature qualification makes no global novelty or priority claim: Burai-Mako-Szokol 2019 and the full strongly Schur-convex-sums chapter remain unread. Independent source fidelity and prefreeze review remain separate from the kernel proof."))), DescribeRole.Theorem)
        )));
}

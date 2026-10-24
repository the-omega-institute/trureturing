using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class InteriorPathTransferConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.";
    private const string SourceGid = "D5/L/GraphInvariants/kirkland2019rationalweightspst";
    private const string SecondSourceGid = "D5/L/GraphInvariants/bailey2024orthogonalpst";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(SourceGid);
    private static readonly LibraryNoteRef SecondSource = LibraryNoteRef.Create(SecondSourceGid);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-vertex weighted path transfers interior states but never transfers endpoint states.",
        H("Interior perfect state transfer without endpoint transfer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interior-path-transfer-converse-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The interior-to-endpoint transfer assertion"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source, SecondSource),
                Blocks(
                    Paragraph(Text(
                        "For a path on the vertices 0 through m, RationalWeightPathTransfer.pathHamiltonian r q is the complex symmetric tridiagonal matrix "
                            + "whose diagonal entries are the real potentials q and whose two adjacent off-diagonal entries on edge {k,k+1} are the real edge weight r(k), included in the complex numbers. "
                            + "RationalWeightPathTransfer.HasPST J t a b means that the squared modulus of the (a,b) entry of exp(itJ) is one. "
                            + "The assertion quantifies over every natural m at least three, every strictly positive edge-weight function r, every real potential function q, "
                            + "and every interior vertex j distinct from its reflection. Fin.val is the inclusion of a finite vertex index into the natural numbers, "
                            + "Fin.rev j has value m minus Fin.val j, and Fin.last m is the endpoint with value m; the subtractions in the vertex conditions are natural-number subtractions. "
                            + "Perfect transfer at some positive time t between j and its reflection is asserted to imply endpoint transfer at some positive time s, which need not equal t.")),
                    Paragraph(Text(
                        "Kirkland, McLaren, Pereira, Plosker and Zhang prove this converse when no eigenvector vanishes at the chosen interior vertex "
                            + "and ask whether that hypothesis can be removed (arXiv:1708.03283v2, main.tex, lines 309–315): "),
                        Ref(SourceGid), Text(
                        ". The displayed assertion expresses that question for distinct mirror interior vertices and positive edge weights. "
                            + "Bailey restates the converse with its hypothesis at new.tex, lines 425–427, and lists the general converse as open at line 602 "
                            + "of arXiv:2412.16351v1: "), Ref(SecondSourceGid), Text("."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("interior-path-transfer-converse-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A five-vertex counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take m = 4, zero potentials, edge weights (2√2, √5, √5, 2√2), and j = 1, whose reflection is 3. "
                            + "All four weights are positive. Write J for this path Hamiltonian and e₀,…,e₄ for the coordinate vectors. "
                            + "Its diagonal is zero; the only nonzero entries are J₀₁ = J₁₀ = J₃₄ = J₄₃ = 2√2 and J₁₂ = J₂₁ = J₂₃ = J₃₂ = √5.")),
                    Paragraph(Text(
                        "Direct multiplication gives the zero-eigenvalue vector h = (−√5, 0, 2√2, 0, −√5), "
                            + "the vectors f₊ = (1, 1, 0, −1, −1) and f₋ = (1, −1, 0, 1, −1) with eigenvalues 2√2 and −2√2, "
                            + "and the vectors g₊ = (2, 3, √2√5, 3, 2) and g₋ = (2, −3, √2√5, −3, 2) with eigenvalues 3√2 and −3√2. "
                            + "For every eigenvector f with eigenvalue E, exponentiation gives exp(isJ)f = exp(isE)f.")),
                    Paragraph(Text(
                        "The two interior coordinate vectors decompose as e₁ = f₊/4 − f₋/4 + g₊/12 − g₋/12 "
                            + "and e₃ = −f₊/4 + f₋/4 + g₊/12 − g₋/12. "
                            + "At the positive time t = 2π/(2√2), the phases of the eigenvalues 2√2 and −2√2 are one, "
                            + "whereas those of 3√2 and −3√2 are minus one. "
                            + "Applying these phases to the decomposition of e₃ gives exp(itJ)e₃ = −e₁. "
                            + "Thus the (1,3) entry is −1 and its squared modulus is one, proving perfect transfer between the interior pair.")),
                    Paragraph(Text(
                        "Suppose now that there is endpoint transfer at a real time s, and write γ = exp(isJ)₀₄. "
                            + "To obtain its column condition, consider the Hermitian matrix A = (s/π)J. "
                            + "Its exponential at time π is exp(isJ), so endpoint transfer and unitarity make the fourth column zero away from row zero: "
                            + "exp(isJ)ₓ₄ is γ when x = 0 and zero otherwise. "
                            + "Since J equals its transpose, exp(isJ) also equals its transpose. "
                            + "Evaluating exp(isJ)f = exp(isE)f at coordinate 4 for an eigenvector f therefore gives exp(isE)f₄ = γf₀.")),
                    Paragraph(Text(
                        "Apply this identity first to h. Its eigenvalue is zero and its equal endpoint entries −√5 are nonzero, so γ = 1. "
                            + "Next apply it to f₊, whose endpoint entries are 1 and −1: exp(is2√2) = −1. "
                            + "Finally apply it to g₊, whose endpoint entries are both 2: exp(is3√2) = 1.")),
                    Paragraph(Text(
                        "The two scalar exponential identities yield integers k and l such that s(2√2)/π = 2k + 1 and s(3√2)/π = 2l, "
                            + "with the integers included in the real numbers in these equations. "
                            + "But 3[s(2√2)/π] = 2[s(3√2)/π], so 6k + 3 = 4l. "
                            + "This equality holds between integers and is impossible, since its left side is odd and its right side is even. "
                            + "Thus there is no endpoint transfer at any real time s. "
                            + "Applying the asserted implication to m = 4, these positive weights, zero potentials, and j = 1 would give endpoint transfer at a positive time, a contradiction. "
                            + "The zero-eigenvalue vector vanishes at both interior vertices and therefore imposes no interior phase condition, while its nonzero endpoint entries force γ = 1."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kirkland-2019-interior-pst-converse-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimFormula()
    {
        Formula m = X("m"), r = X("r"), q = X("q"), j = X("j");
        Formula vertices = FinOf(Parenthesized(Add(m, D(1))));
        Formula index = Typed(At(Qualified("Fin", "val"), j), Naturals());
        Formula matrix = Parenthesized(At(Owner("pathHamiltonian"), r, q));
        Formula interior = Some("t", Reals(), And(
            Less(Typed(D(0), Reals()), X("t")),
            At(Owner("HasPST"), matrix, X("t"), j, At(Qualified("Fin", "rev"), j))));
        Formula endpoints = Some("s", Reals(), And(
            Less(Typed(D(0), Reals()), X("s")),
            At(Owner("HasPST"), matrix, X("s"), Typed(D(0), vertices), At(Qualified("Fin", "last"), m))));
        Formula body = Implies(interior, endpoints);
        body = Implies(NotEqual(index, Parenthesized(Subtract(m, index))), body);
        body = Implies(LE(index, Parenthesized(Subtract(m, D(1)))), body);
        body = Implies(LE(D(1), index), body);
        body = All("q", Arrow(vertices, Reals()), All("j", vertices, body));
        body = Implies(All("k", FinOf(m), Less(Typed(D(0), Reals()), At(r, X("k")))), body);
        body = All("r", Arrow(FinOf(m), Reals()), body);
        body = All("m", Naturals(), Implies(LE(D(3), m), body));
        return new Formula.Logic(Parenthesized(Local("claim")), FormulaLogicOperator.Iff, Parenthesized(body));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("InteriorPathTransferConverseRefutation", name);
    private static Formula Owner(string name) => Qualified("RationalWeightPathTransfer", name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
}

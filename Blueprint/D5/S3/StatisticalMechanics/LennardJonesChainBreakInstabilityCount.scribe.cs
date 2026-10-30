using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class LennardJonesChainBreakInstabilityCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/rodrigueskevrekidisdobson2019nbreak");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a clamped steady Lennard-Jones chain with positive pre-stretch, positive bond lengths, at least one free particle and k ≥ 1 broken bonds, the positive force-Jacobian eigenvalue count lies between k − 1 and k.",
        H("The instability count of a Lennard-Jones chain"),
        Blocks(
            Definition("lj-potential", "ljPotential", "The Lennard-Jones interaction", PotentialFormula(),
                "The interaction potential is the difference of the inverse twelfth power and twice the inverse sixth power. "
                    + "This is equation (2) of oscillatorsNN_resubmit.tex, lines 185-189. "
                    + "The exponents are integers and the values are real. Integer powers give a total real function, "
                    + "including at zero; the instability statement below assumes positive bond lengths."),
            Definition("inflection-point", "inflectionPoint", "The inflection length", InflectionFormula(),
                "The inflection length is the real sixth root of thirteen sevenths, as in "
                    + "oscillatorsNN_resubmit.tex, lines 197-200. The exponent one sixth is real. "
                    + "A positive bond length is broken precisely when it is strictly greater than this length "
                    + "(lines 280-283); equality is excluded from the broken-bond count."),
            Definition("bond-length", "bondLength", "Successive particle separations", BondFormula(),
                "The displacement vector u has m plus two coordinates, including both endpoints. "
                    + "The bond indexed by j joins coordinates j.castSucc and j.succ, and its length is "
                    + "the pre-stretch d plus the right displacement minus the left displacement. "
                    + "Thus the m plus one bonds have indices starting at zero. This expresses the separations "
                    + "in the potential energy in oscillatorsNN_resubmit.tex, lines 161-170."),
            Definition("force", "force", "The force at a free particle", ForceFormula(),
                "For the free particle indexed by n, the force is the derivative of the potential at "
                    + "the right bond length minus its derivative at the left bond length. "
                    + "The particle has coordinate n plus one in u. This is equation (1) of "
                    + "oscillatorsNN_resubmit.tex, lines 175-181, with the free particles indexed from zero."),
            Definition("jacobian", "jacobian", "The tridiagonal force Jacobian", JacobianFormula(),
                "Let c(j) be the second derivative of the potential at bond j. "
                    + "The diagonal entry at n is minus the sum of the two adjacent curvatures. "
                    + "The entry immediately to its right is the right-bond curvature, and the symmetric "
                    + "entry immediately to its left is the corresponding shared-bond curvature; all other entries vanish. "
                    + "Fin.val makes both conversions of the finite indices to natural numbers explicit in each adjacency test. "
                    + "This is the force Jacobian in the linearization of oscillatorsNN_resubmit.tex, lines 230-250."),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The two-sided count for a clamped steady chain"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every m at least one and every positive pre-stretch d, take a displacement "
                    + "vector u with both endpoints zero, zero force at each free particle, and all bond lengths positive. "
                    + "If exactly k bonds are broken, with k at least one, then for every Hermitian witness h "
                    + "of the force Jacobian, the number of its strictly positive eigenvalues lies between "
                    + "k minus one and k. The subtraction and both finite cardinalities are natural-valued, "
                    + "and eigenvalues are counted with multiplicity by their indices in Fin m. "
                    + "The explicit argument of Fin.last is m plus one, so it selects the last of the m plus two coordinates. "
                    + "This is the positive-Jacobian-eigenvalue reading of the conjecture in "
                    + "oscillatorsNN_resubmit.tex, lines 55-59. Its interpretation as unstable pairs follows "
                    + "the squared spectral parameter in the linearization, lines 230-250."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The curvature and dimension argument"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For r positive, differentiating the interaction twice gives "
                        + "φ″(r) = 12(13 − 7r⁶)/r¹⁴. The first derivative is "
                        + "−12r⁻¹³ + 12r⁻⁷; its expression holds throughout a neighbourhood of r, "
                        + "so it can be differentiated again there. Since the denominator r¹⁴ is positive "
                        + "and taking a positive sixth root preserves strict order, "
                        + "φ″(r) < 0 holds exactly when inflectionPoint < r.")),
                    Paragraph(Text(
                        "Define the real matrix b with m plus one rows and m columns by "
                        + "b(j,n) = 1 if j = n.castSucc, minus 1 if j = n.succ, and zero otherwise, "
                        + "and put c(j) = φ″(bondLength d u j). Expanding the matrix product entry by entry "
                        + "gives jacobian d u = −bᵀ diag(c)b. The two nonzero entries of each column "
                        + "give the diagonal and neighbouring entries in the displayed Jacobian; "
                        + "the remaining entries are zero.")),
                    Paragraph(Text(
                        "The map x ↦ bx is injective. For m = 0 this follows from the unique vector "
                        + "in the zero-dimensional domain. For positive m, extend scalars to the algebraic closure "
                        + "of the reals. The two standard face maps insert a zero after or before the m coordinates. "
                        + "Their matrix pencil at identity factors and coefficients 1 and −1 is the scalar extension "
                        + "of b, and its full-rank property gives rank m. "
                        + "Rank-nullity makes its kernel zero. Applying this injectivity to the images of two real "
                        + "vectors and using injectivity of the scalar inclusion proves injectivity over the reals. "
                        + "Consequently the range of b has dimension m in a space of dimension m plus one.")),
                    Paragraph(Text(
                        "Pulling back the diagonal quadratic form along b and negating it yields "
                        + "hermForm(jacobian d u,x) = −∑ⱼ c(j)(bx)(j)². "
                        + "This follows from the quadratic-form identity for a transpose product and "
                        + "the coordinate formula for a diagonal matrix.")),
                    Paragraph(Text(
                        "For the lower bound, let e be the coordinate subspace supported on the broken bonds, "
                        + "and let v be its inverse image under b. The broken-bond count gives dim e = k. "
                        + "Injectivity identifies v with range(b) ∩ e. The dimension identity for a sum "
                        + "and intersection of subspaces, together with dim range(b) = m and the ambient "
                        + "dimension m plus one, gives dim v ≥ k − 1. "
                        + "For a nonzero x in v, every unbroken coordinate of bx is zero, "
                        + "and injectivity ensures that some broken coordinate is nonzero. "
                        + "Each broken curvature is strictly negative, so every term c(j)(bx)(j)² "
                        + "is nonpositive and at least one is negative. Thus the Jacobian quadratic form "
                        + "is positive definite on v. The Hermitian positive-index bound then gives "
                        + "k − 1 ≤ dim v ≤ the number of positive eigenvalues.")),
                    Paragraph(Text(
                        "For the upper bound, choose a subspace w on which the Jacobian quadratic form "
                        + "is positive definite and whose dimension equals the number of positive eigenvalues. "
                        + "Map x in w to the broken coordinates of bx. This linear map is injective: "
                        + "if those coordinates vanish, all remaining curvatures are nonnegative, so "
                        + "−∑ⱼ c(j)(bx)(j)² ≤ 0. Positive definiteness forces x = 0. "
                        + "The target is the real coordinate space on exactly k broken bonds, of dimension k, "
                        + "and therefore dim w ≤ k. Combining the lower and upper bounds proves claim "
                        + "for all its stated parameters. The argument uses positive bond lengths and their "
                        + "broken-bond count; the steady-state, endpoint, and positive-pre-stretch hypotheses "
                        + "are retained in the statement. It asserts no existence of steady states with a specified count."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rodrigues-kevrekidis-dobson-2019-n-break-instability-count"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PotentialFormula() => All("r", Reals(),
        Equal(Typed(LocalCall("ljPotential", X("r")), Reals()),
            Subtract(Power(X("r"), Typed(new Formula.Negate(D(1, 2)), Integers())),
                Multiply(Real(D(2)), Power(X("r"), Typed(new Formula.Negate(D(6)), Integers()))))));

    private static Formula InflectionFormula() =>
        Equal(Typed(Local("inflectionPoint"), Reals()),
            Power(Divide(Real(D(1, 3)), Real(D(7))), Divide(Real(D(1)), Real(D(6)))));

    private static Formula BondFormula() => ChainBinders(All("j", BondIndex(),
        Equal(Typed(LocalCall("bondLength", X("d"), X("u"), X("j")), Reals()),
            Subtract(Add(X("d"), At(X("u"), Succ(X("j")))), At(X("u"), CastSucc(X("j")))))));

    private static Formula ForceFormula() => ChainBinders(All("n", FinOf(X("m")),
        Equal(Typed(LocalCall("force", X("d"), X("u"), X("n")), Reals()),
            Subtract(At(Qualified("deriv"), Local("ljPotential"), Bond(Succ(X("n")))),
                At(Qualified("deriv"), Local("ljPotential"), Bond(CastSucc(X("n"))))))));

    private static Formula JacobianFormula()
    {
        Formula curvature = LambdaOf("j", BondIndex(),
            At(Qualified("deriv"), At(Qualified("deriv"), Local("ljPotential")), Bond(X("j"))));
        Formula entries = If(Equal(X("n"), X("q")),
            Subtract(new Formula.Negate(At(X("c"), CastSucc(X("n")))), At(X("c"), Succ(X("n")))),
            If(Equal(Add(Val(X("n")), Natural(D(1))), Val(X("q"))), At(X("c"), Succ(X("n"))),
                If(Equal(Add(Val(X("q")), Natural(D(1))), Val(X("n"))), At(X("c"), Succ(X("q"))), Real(D(0)))));
        Formula value = LambdaOf("n", FinOf(X("m")), LambdaOf("q", FinOf(X("m")),
            LetOf("c", Arrow(BondIndex(), Reals()), curvature, entries)));
        return ChainBinders(Equal(Typed(LocalCall("jacobian", X("d"), X("u")),
            At(Qualified("Matrix"), FinOf(X("m")), FinOf(X("m")), Reals())), Parenthesized(value)));
    }

    private static Formula ClaimBody()
    {
        Formula broken = Card(At(Qualified("Finset", "filter"),
            LambdaOf("j", BondIndex(), Less(Local("inflectionPoint"), Bond(X("j")))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), BondIndex()))));
        Formula positive = Card(At(Qualified("Finset", "filter"),
            LambdaOf("i", FinOf(X("m")), Less(Real(D(0)),
                At(Qualified("Matrix", "IsHermitian", "eigenvalues"), X("h"), X("i")))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), FinOf(X("m"))))));
        Formula bounds = Conjunction(LessEqual(Subtract(X("k"), Natural(D(1))), positive),
            LessEqual(positive, X("k")));
        Formula body = All("k", Naturals(), Implication(LessEqual(Natural(D(1)), X("k")),
            Implication(Equal(broken, X("k")), All("h",
                At(Qualified("Matrix", "IsHermitian"), LocalCall("jacobian", X("d"), X("u"))), bounds))));
        body = Implication(All("j", BondIndex(), Less(Real(D(0)), Bond(X("j")))), body);
        body = Implication(All("n", FinOf(X("m")), Equal(LocalCall("force", X("d"), X("u"), X("n")), Real(D(0)))), body);
        body = Implication(Equal(At(X("u"), At(Qualified("Fin", "last"), Add(X("m"), Natural(D(1))))), Real(D(0))), body);
        body = Implication(Equal(At(X("u"), Typed(D(0), ParticleIndex())), Real(D(0))), body);
        return All("m", Naturals(), Implication(LessEqual(Natural(D(1)), X("m")),
            All("d", Reals(), Implication(Less(Real(D(0)), X("d")), All("u", Displacements(), body)))));
    }

    private static Formula ChainBinders(Formula body) =>
        All("m", Naturals(), All("d", Reals(), All("u", Displacements(), body)));
    private static Formula ParticleIndex() => FinOf(Add(X("m"), Natural(D(2))));
    private static Formula BondIndex() => FinOf(Add(X("m"), Natural(D(1))));
    private static Formula Displacements() => Arrow(ParticleIndex(), Reals());
    private static Formula Bond(Formula j) => LocalCall("bondLength", X("d"), X("u"), j);
    private static Formula Succ(Formula j) => At(Qualified("Fin", "succ"), j);
    private static Formula CastSucc(Formula j) => At(Qualified("Fin", "castSucc"), j);
    private static Formula Val(Formula j) => Typed(At(Qualified("Fin", "val"), j), Naturals());
    private static Formula Card(Formula set) => Typed(At(Qualified("Finset", "card"), set), Naturals());
    private static Formula Local(string name) => Qualified("D5", "S3", "StatisticalMechanics",
        "LennardJonesChainBreakInstabilityCount", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Natural(Formula value) => Typed(value, Naturals());
    private static Formula Real(Formula value) => Typed(value, Reals());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula LetOf(string name, Formula type, Formula value, Formula body) =>
        Seq(Qualified("let"), Sp, Typed(X(name), type), Sp, Eq, Sp, Parenthesized(value), Semi, Sp, Parenthesized(body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), Parenthesized(condition), Parenthesized(yes), Parenthesized(no));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Implication(Formula premise, Formula conclusion) => Arrow(premise, conclusion);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
}

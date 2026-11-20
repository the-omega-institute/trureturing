using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.CompactGroups;

internal sealed class SchurOrthogonalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/CompactGroups/SchurOrthogonality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a compact group with Haar measure and continuous irreducible representations, one of them on a finite-dimensional complex normed space, the integral of a product of matrix coefficients, the second taken at the inverse group element, vanishes for inequivalent representations and equals the product of the crossed coefficients divided by the dimension for one representation and a Haar probability measure.",
        H("Schur Orthogonality of Matrix Coefficients on Compact Groups"),
        Blocks(
            Node("inequivalent", "integral_dual_mul_dual_inv_eq_zero",
                "Matrix coefficients of inequivalent irreducible representations are orthogonal",
                StatementSource.FromAuthor(ZeroFormula()),
                Paragraph(Text("Let G be a compact topological group carrying its Borel sigma-algebra and a Haar measure mu. Let rho be a representation of G on a finite-dimensional complex normed space V, and sigma a representation of G on a complex vector space W, which carries no topology. Both are irreducible: each is nonzero and has no invariant subspaces other than 0 and the whole space. Assume that there is no equivalence of representations from rho to sigma, that is, no linear isomorphism from V onto W intertwining rho(g) with sigma(g) for every g, that every orbit map g -> rho(g)(v) is continuous, and that phi is a complex linear functional on V and psi a complex linear functional on W such that every coefficient g -> psi(sigma(g)(w)) is continuous. The theorem states that for all v in V and w in W the integral over G, with respect to mu, of phi(rho(g)(v)) * psi(sigma(g^(-1))(w)) is 0. In the formula Dual(C, V) is the space of complex linear functionals on V, Equiv(rho, sigma) the type of equivalences from rho to sigma, and the integration variable is g.")),
                Paragraph(Text("For fixed v the map T sending x in W to the vector-valued integral of psi(sigma(g^(-1))(x)) rho(g)(v) is complex linear. The integrand is continuous on the compact group, hence integrable for the finite measure mu, and the integral exists because the finite-dimensional space V is complete. Left invariance of mu turns T(sigma(h)(x)) into the integral of psi(sigma((h g)^(-1))(sigma(h)(x))) rho(h g)(v) = psi(sigma(g^(-1))(x)) rho(h)(rho(g)(v)), and moving the linear map rho(h) out of the integral gives T(sigma(h)(x)) = rho(h)(T(x)); so T intertwines sigma with rho. Applying phi to T(w) gives the integral of the theorem. By Schur's lemma a nonzero intertwining map between irreducible representations is bijective, hence an equivalence; since sigma and rho are not equivalent, T = 0 and the integral vanishes. Only the left invariance of mu enters.")),
                Paragraph(Text("Neither irreducibility hypothesis can be dropped, nor inequivalence. If rho and sigma are both the trivial representation on C, with phi and psi the identity and v = w = 1, every hypothesis except inequivalence holds and the integral is the total mass mu(G), which is positive for a Haar measure on a compact group. If rho is the trivial representation on C and sigma the trivial representation on C x C, the two are inequivalent because their dimensions differ and sigma is reducible; with phi the identity, psi the first coordinate, v = 1 and w = (1, 0) the integral is again mu(G). Exchanging the roles, with rho trivial on C x C and sigma trivial on C, shows the same for the irreducibility of rho.")),
                Paragraph(Text("In the classical unitary setting the statement takes a familiar form. If V and W are finite-dimensional complex inner product spaces, with the inner product conjugate linear in its first argument, and rho and sigma act by unitary operators, then sigma(g^(-1)) is the adjoint of sigma(g). Taking phi the functional x -> <v, x> and psi the functional x -> <w', x>, one has psi(sigma(g^(-1))(w)) = <sigma(g)(w'), w>, the complex conjugate of <w, sigma(g)(w')>, so the theorem applied to the vectors v' and w shows that the integral of <v, rho(g)(v')> times the complex conjugate of <w, sigma(g)(w')> is 0 for inequivalent irreducible unitary representations. This consequence follows by the substitution just described and is not a separate statement here.")),
                Paragraph(Text("These are the orthogonality relations of Schur for matrix coefficients, in the form for compact groups in which the average over a finite group is replaced by the integral against Haar measure; the relations are classical. The form given here uses arbitrary linear functionals in place of an invariant inner product and does not assume that the representations are unitary."))),
            Node("self", "integral_dual_mul_dual_inv_self",
                "The integral of a product of matrix coefficients of one irreducible representation",
                StatementSource.FromAuthor(SelfFormula()),
                Paragraph(Text("Let G be a compact topological group carrying its Borel sigma-algebra and a Haar measure mu of total mass 1. Let rho be an irreducible representation of G on a finite-dimensional complex normed space V such that every orbit map g -> rho(g)(v) is continuous. The theorem states that for complex linear functionals phi and psi on V and vectors v and w in V, the integral over G, with respect to mu, of phi(rho(g)(v)) * psi(rho(g^(-1))(w)) equals phi(w) * psi(v) / dim V, where dim V = finrank(C, V) is the complex dimension of V, read as a complex number. No continuity hypothesis on psi is needed, because every linear functional on a finite-dimensional normed space is continuous.")),
                Paragraph(Text("As for inequivalent representations, the map T sending x in V to the integral of psi(rho(g^(-1))(x)) rho(g)(v) is linear and, by left invariance of mu, intertwines rho with itself, and phi(T(w)) is the integral of the theorem. Since V is finite-dimensional, rho is irreducible and the complex field is algebraically closed, Schur's lemma gives a complex number c with T(x) = c x for all x. To find c, take a basis b(1), ..., b(n) of V with coordinate functionals b*(1), ..., b*(n), where n = dim V. The trace of T is n c, and it is also the sum over i of b*(i)(T(b(i))), which is the integral of the sum over i of psi(rho(g^(-1))(b(i))) b*(i)(rho(g)(v)). By linearity of psi and rho(g^(-1)) this sum is psi(rho(g^(-1))(rho(g)(v))) = psi(v), whose integral is psi(v) because mu has total mass 1. Hence n c = psi(v). An irreducible representation is nonzero, so n is positive, c = psi(v) / n, and the integral is phi(c w) = phi(w) * psi(v) / n.")),
                Paragraph(Text("The normalization of mu and the irreducibility of rho cannot be dropped. For the trivial group, V = C with the trivial representation, phi and psi the identity and v = w = 1, the left side is the total mass of mu and the right side is 1, so a Haar measure of any other total mass violates the formula. For the trivial representation of a compact group on C x C, which is reducible, with mu of total mass 1, phi and psi the first coordinate and v = w = (1, 0), the left side is 1 while the right side is 1/2. Finite dimensionality of V is used for the completeness of V, the continuity of psi, the scalar form of Schur's lemma and the trace.")),
                Paragraph(Text("For a unitary irreducible representation on a finite-dimensional complex inner product space, with the inner product conjugate linear in its first argument, take phi the functional x -> <v, x> and psi the functional x -> <w', x>. Since rho(g^(-1)) is the adjoint of rho(g), psi(rho(g^(-1))(w)) is the complex conjugate of <w, rho(g)(w')>, and the theorem applied to the vectors v' and w gives the classical relation: the integral of <v, rho(g)(v')> times the complex conjugate of <w, rho(g)(w')> equals <v, w> <w', v'> / dim V. This consequence follows by the substitution just described and is not a separate statement here.")),
                Paragraph(Text("This is the second of the classical Schur orthogonality relations for compact groups. The statement for arbitrary linear functionals contains the unitary form and does not assume unitarity; only left invariance and the normalization of mu are used.")))))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, params DocumentBlock[] paragraphs) =>
        Describe.Lean(
            DescribeId.Create("schur-orthogonality-" + id),
            DeclarationHandle.Create(Prefix + selector),
            H(title),
            statement,
            AssessedProvenance.FromRepo(),
            Blocks(paragraphs),
            DescribeRole.Theorem);

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula OpApp(string name, params Formula[] arguments) => App(Op(name), arguments);
    private static Formula Inst(Formula content) => Seq(OpenBracket, content, CloseBracket, Comma, Sp);
    private static Formula Parenthesized(Formula content) => Seq(Open, content, Close);
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));

    /// <summary>A universal binder written with a symbol, rendered like a Bind node.</summary>
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, SemiSpace, Sp, body);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Inverse(Formula x) => new Formula.Power(x, Seq(Minus, D(1)));

    /// <summary>The value of a representation at a group element, applied to a vector.</summary>
    private static Formula Act(Formula representation, Formula element, Formula vector) =>
        App(App(representation, element), vector);

    private static Formula Integral(Formula measure, Formula variable, Formula integrand) =>
        Seq(Int, Sp, integrand, Sp, Thin, Mathrm, Grp(F.Id("d")), App(measure, variable));

    private static Formula ContinuousIn(Formula variable, Formula body) =>
        OpApp("Continuous", Seq(variable, Sp, Mapsto, Sp, body));

    /// <summary>The binders shared by both theorems up to the measure and the space V.</summary>
    private static Formula GroupAndMeasure(Formula after)
    {
        Formula g = F.Id("G");
        return Seq(
            Inst(OpApp("Group", g)),
            Inst(OpApp("TopologicalSpace", g)),
            Inst(OpApp("IsTopologicalGroup", g)),
            Inst(OpApp("CompactSpace", g)),
            Inst(OpApp("MeasurableSpace", g)),
            Inst(OpApp("BorelSpace", g)),
            All(Mu, OpApp("Measure", g), Seq(
                Inst(OpApp("IsHaarMeasure", Mu)),
                Inst(OpApp("NormedAddCommGroup", F.Id("V"))),
                Inst(OpApp("NormedSpace", Complexes, F.Id("V"))),
                Inst(OpApp("FiniteDimensional", Complexes, F.Id("V"))),
                after)));
    }

    private static Formula ZeroFormula()
    {
        Formula G = F.Id("G"), V = F.Id("V"), W = F.Id("W"), g = F.Id("g"), v = F.Id("v"), w = F.Id("w");
        Formula integrand = Mul(App(Phi, Act(Rho, g, v)), App(Psi, Act(SigmaLower, Inverse(g), w)));
        Formula conclusion = ForAll("v", V, ForAll("w", W, Equal(Integral(Mu, g, integrand), D(0))));
        Formula afterFunctionals = Implies(
            Parenthesized(ForAll("w", W, ContinuousIn(g, App(Psi, Act(SigmaLower, g, w))))),
            conclusion);
        Formula functionals = All(Phi, OpApp("Dual", Complexes, V),
            All(Psi, OpApp("Dual", Complexes, W), afterFunctionals));
        Formula afterRepresentations = Seq(
            Inst(OpApp("IsIrreducible", Rho)),
            Inst(OpApp("IsIrreducible", SigmaLower)),
            Implies(OpApp("IsEmpty", OpApp("Equiv", Rho, SigmaLower)),
                Implies(Parenthesized(ForAll("v", V, ContinuousIn(g, Act(Rho, g, v)))), functionals)));
        Formula representations = Seq(
            Inst(OpApp("AddCommGroup", W)),
            Inst(OpApp("Module", Complexes, W)),
            All(Rho, OpApp("Representation", Complexes, G, V),
                All(SigmaLower, OpApp("Representation", Complexes, G, W), afterRepresentations)));
        return Disp(ForAll("G", TypeStar, ForAll("V", TypeStar, ForAll("W", TypeStar,
            GroupAndMeasure(representations)))));
    }

    private static Formula SelfFormula()
    {
        Formula G = F.Id("G"), V = F.Id("V"), g = F.Id("g"), v = F.Id("v"), w = F.Id("w");
        Formula integrand = Mul(App(Phi, Act(Rho, g, v)), App(Psi, Act(Rho, Inverse(g), w)));
        Formula right = new Formula.Fraction(Mul(App(Phi, w), App(Psi, v)), OpApp("finrank", Complexes, V));
        Formula conclusion = All(Phi, OpApp("Dual", Complexes, V), All(Psi, OpApp("Dual", Complexes, V),
            ForAll("v", V, ForAll("w", V, Equal(Integral(Mu, g, integrand), right)))));
        Formula afterMeasure = Seq(
            Inst(OpApp("IsProbabilityMeasure", Mu)),
            All(Rho, OpApp("Representation", Complexes, G, V), Seq(
                Inst(OpApp("IsIrreducible", Rho)),
                Implies(Parenthesized(ForAll("v", V, ContinuousIn(g, Act(Rho, g, v)))), conclusion))));
        return Disp(ForAll("G", TypeStar, ForAll("V", TypeStar, GroupAndMeasure(afterMeasure))));
    }
}

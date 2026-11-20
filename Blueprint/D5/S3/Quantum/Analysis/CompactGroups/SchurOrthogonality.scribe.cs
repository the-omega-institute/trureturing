using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.CompactGroups;

internal sealed class SchurOrthogonalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/CompactGroups/SchurOrthogonality.";
    private static LibraryNoteRef Folland => LibraryNoteRef.Create("D5/L/Fourier/folland2016course");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let G be a compact group with a finite left-invariant measure mu, K the field of real or of complex numbers, rho a representation of G on a finite-dimensional normed space over K with continuous orbit maps, sigma a representation of G on a vector space over K, both irreducible, and phi and psi linear functionals such that every coefficient g -> psi(sigma(g)(w)) is continuous. The integral of phi(rho(g)(v)) * psi(sigma(g^(-1))(w)) against mu vanishes when rho and sigma are inequivalent. Over the complex numbers and for sigma = rho it equals the total mass of mu times phi(w) * psi(v), divided by the dimension.",
        H("Schur Orthogonality of Matrix Coefficients on Compact Groups"),
        Blocks(
            Node("inequivalent", "integral_dual_mul_dual_inv_eq_zero",
                "Matrix coefficients of inequivalent irreducible representations are orthogonal",
                StatementSource.FromAuthor(ZeroFormula()),
                Paragraph(Text("Let G be a compact topological group carrying its Borel sigma-algebra and a finite measure mu that is invariant under left translations; in the formula these are the hypotheses IsMulLeftInvariant(mu) and IsFiniteMeasure(mu). Let K be a field carrying the structure RCLike(K), that is, the field of real numbers or the field of complex numbers. Let rho be a representation of G on a finite-dimensional normed space V over K, and sigma a representation of G on a vector space W over K, which carries no topology. Both are irreducible: each is nonzero and has no invariant subspaces other than 0 and the whole space. Assume that there is no equivalence of representations from rho to sigma, that is, no K-linear isomorphism from V onto W intertwining rho(g) with sigma(g) for every g, that every orbit map g -> rho(g)(v) is continuous, and that phi is a K-linear functional on V and psi a K-linear functional on W such that every coefficient g -> psi(sigma(g)(w)) is continuous. The theorem states that for all v in V and w in W the integral over G, with respect to mu, of phi(rho(g)(v)) * psi(sigma(g^(-1))(w)) is 0. In the formula Dual(K, V) is the space of K-linear functionals on V, Equiv(rho, sigma) the type of equivalences from rho to sigma, and the integration variable is g.")),
                Paragraph(Text("For fixed v the map T sending x in W to the vector-valued integral of psi(sigma(g^(-1))(x)) rho(g)(v) is K-linear; the integral is taken in V regarded as a real normed space by restriction of scalars, and K-linear maps commute with it. The integrand is continuous on the compact group, hence measurable for the Borel sigma-algebra and integrable for the finite measure mu, and the integral exists because the finite-dimensional space V is complete. Left invariance of mu turns T(sigma(h)(x)) into the integral of psi(sigma((h g)^(-1))(sigma(h)(x))) rho(h g)(v) = psi(sigma(g^(-1))(x)) rho(h)(rho(g)(v)), and moving the linear map rho(h) out of the integral gives T(sigma(h)(x)) = rho(h)(T(x)); so T intertwines sigma with rho. Applying phi to T(w) gives the integral of the theorem. By Schur's lemma a nonzero intertwining map between irreducible representations is bijective, hence an equivalence; since sigma and rho are not equivalent, T = 0 and the integral vanishes. Only the left invariance and the finiteness of mu, together with the Borel structure of G through which continuity gives integrability, enter the proof, and for the zero measure the conclusion holds trivially. This form is no wider than the classical one: on a compact group every nonzero finite left-invariant Borel measure is a Haar measure, so apart from the zero measure the hypotheses describe exactly the Haar measures, with the total mass mu(G) left free.")),
                Paragraph(Text("Neither irreducibility hypothesis can be dropped, nor inequivalence, once mu is not the zero measure, for instance for a Haar measure. If rho and sigma are both the trivial representation on K, with phi and psi the identity and v = w = 1, every hypothesis except inequivalence holds and the integral is the total mass mu(G), which is then positive. If rho is the trivial representation on K and sigma the trivial representation on K x K, the two are inequivalent because their dimensions differ and sigma is reducible; with phi the identity, psi the first coordinate, v = 1 and w = (1, 0) the integral is again mu(G). Exchanging the roles, with rho trivial on K x K and sigma trivial on K, shows the same for the irreducibility of rho.")),
                Paragraph(Text("In the classical unitary setting over the complex numbers the statement takes a familiar form. If V and W are finite-dimensional complex inner product spaces, with the inner product conjugate linear in its first argument, and rho and sigma act by unitary operators, then sigma(g^(-1)) is the adjoint of sigma(g). Taking phi the functional x -> <v, x> and psi the functional x -> <w', x>, one has psi(sigma(g^(-1))(w)) = <sigma(g)(w'), w>, the complex conjugate of <w, sigma(g)(w')>, so the theorem applied to the vectors v' and w shows that the integral of <v, rho(g)(v')> times the complex conjugate of <w, sigma(g)(w')> is 0 for inequivalent irreducible unitary representations. This consequence follows by the substitution just described and is not stated as a theorem here.")),
                Paragraph(Text("These are the orthogonality relations of Schur for matrix coefficients, in the form for compact groups in which the average over a finite group is replaced by the integral against Haar measure; the relations are classical and belong to the background of abstract harmonic analysis. The form given here uses arbitrary linear functionals in place of an invariant inner product, does not assume that the representations are unitary, holds over the real as well as the complex numbers, and asks of the measure only left invariance and finiteness."))),
            Node("self", "integral_dual_mul_dual_inv_self",
                "The integral of a product of matrix coefficients of one irreducible representation",
                StatementSource.FromAuthor(SelfFormula()),
                Paragraph(Text("Let G be a compact topological group carrying its Borel sigma-algebra and a finite measure mu invariant under left translations. Let rho be an irreducible representation of G on a finite-dimensional complex normed space V such that every orbit map g -> rho(g)(v) is continuous. The theorem states that for complex linear functionals phi and psi on V and vectors v and w in V, the integral over G, with respect to mu, of phi(rho(g)(v)) * psi(rho(g^(-1))(w)) equals real(mu, univ) * (phi(w) * psi(v)) / dim V. Here real(mu, univ) is the total mass mu(G), a finite nonnegative real number, and dim V = finrank(C, V) is the complex dimension of V; both are read as complex numbers. No continuity hypothesis on psi is needed, because every linear functional on a finite-dimensional normed space is continuous.")),
                Paragraph(Text("As for inequivalent representations, the map T sending x in V to the integral of psi(rho(g^(-1))(x)) rho(g)(v) is linear and, by left invariance of mu, intertwines rho with itself, and phi(T(w)) is the integral of the theorem. Since V is finite-dimensional, rho is irreducible and the complex field is algebraically closed, Schur's lemma gives a complex number c with T(x) = c x for all x. To find c, take a basis b(1), ..., b(n) of V with coordinate functionals b*(1), ..., b*(n), where n = dim V. The trace of T is n c, and it is also the sum over i of b*(i)(T(b(i))), which is the integral of the sum over i of psi(rho(g^(-1))(b(i))) b*(i)(rho(g)(v)). By linearity of psi and rho(g^(-1)) this sum is psi(rho(g^(-1))(rho(g)(v))) = psi(v), a constant whose integral is mu(G) psi(v). Hence n c = mu(G) psi(v). An irreducible representation is nonzero, so n is positive, c = mu(G) psi(v) / n, and the integral is phi(c w) = mu(G) * (phi(w) * psi(v)) / n. For the zero measure both sides are 0, and the argument covers this case without change.")),
                Paragraph(Text("Remark, not stated as a theorem here: the statement is made over the complex numbers only, because over the real numbers the formula fails. The rotation representation of the circle group on the real plane is irreducible, since no line is invariant under all rotations, but its commutant consists of all a I + b J with J the rotation by a right angle, not only of the scalars, so the scalar form of Schur's lemma is not available. Concretely, for the normalized Haar measure, phi and psi the first coordinate and v = w = (0, 1), the left side is minus the integral of sin(t)^2 over the circle, which is -1/2, while the right side phi(w) * psi(v) / 2 is 0.")),
                Paragraph(Text("The total mass of mu enters as a factor: replacing mu by a positive multiple multiplies both sides by that number, and for a measure of total mass 1, such as a normalized Haar measure, the right side is phi(w) * psi(v) / dim V. The irreducibility of rho cannot be dropped once mu is not the zero measure. For the trivial representation of a compact group on C x C, which is reducible, with phi and psi the first coordinate and v = w = (1, 0), the left side is mu(G) while the right side is mu(G) / 2. Finite dimensionality of V is used for the completeness of V, the continuity of psi, the scalar form of Schur's lemma and the trace.")),
                Paragraph(Text("For a unitary irreducible representation on a finite-dimensional complex inner product space, with the inner product conjugate linear in its first argument, take phi the functional x -> <v, x> and psi the functional x -> <w', x>. Since rho(g^(-1)) is the adjoint of rho(g), psi(rho(g^(-1))(w)) is the complex conjugate of <w, rho(g)(w')>, and the theorem applied to the vectors v' and w gives the classical relation: the integral of <v, rho(g)(v')> times the complex conjugate of <w, rho(g)(w')> equals mu(G) <v, w> <w', v'> / dim V, which is <v, w> <w', v'> / dim V for a normalized Haar measure. This consequence follows by the substitution just described and is not stated as a theorem here.")),
                Paragraph(Text("This is the second of the classical Schur orthogonality relations for compact groups. The statement for arbitrary linear functionals contains the unitary form and does not assume unitarity; only the left invariance and the finiteness of mu enter, together with the Borel structure of G through which continuity gives integrability, and its total mass appears explicitly instead of being normalized to 1."))))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, params DocumentBlock[] paragraphs) =>
        Describe.Lean(
            DescribeId.Create("schur-orthogonality-" + id),
            DeclarationHandle.Create(Prefix + selector),
            H(title),
            statement,
            AssessedProvenance.FromRepo(Folland),
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
    private static Formula GroupAndMeasure(Formula field, Formula after)
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
                Inst(OpApp("IsMulLeftInvariant", Mu)),
                Inst(OpApp("IsFiniteMeasure", Mu)),
                Inst(OpApp("NormedAddCommGroup", F.Id("V"))),
                Inst(OpApp("NormedSpace", field, F.Id("V"))),
                Inst(OpApp("FiniteDimensional", field, F.Id("V"))),
                after)));
    }

    private static Formula ZeroFormula()
    {
        Formula K = F.Id("K"), G = F.Id("G"), V = F.Id("V"), W = F.Id("W");
        Formula g = F.Id("g"), v = F.Id("v"), w = F.Id("w");
        Formula integrand = Mul(App(Phi, Act(Rho, g, v)), App(Psi, Act(SigmaLower, Inverse(g), w)));
        Formula conclusion = ForAll("v", V, ForAll("w", W, Equal(Integral(Mu, g, integrand), D(0))));
        Formula afterFunctionals = Implies(
            Parenthesized(ForAll("w", W, ContinuousIn(g, App(Psi, Act(SigmaLower, g, w))))),
            conclusion);
        Formula functionals = All(Phi, OpApp("Dual", K, V),
            All(Psi, OpApp("Dual", K, W), afterFunctionals));
        Formula afterRepresentations = Seq(
            Inst(OpApp("IsIrreducible", Rho)),
            Inst(OpApp("IsIrreducible", SigmaLower)),
            Implies(OpApp("IsEmpty", OpApp("Equiv", Rho, SigmaLower)),
                Implies(Parenthesized(ForAll("v", V, ContinuousIn(g, Act(Rho, g, v)))), functionals)));
        Formula representations = Seq(
            Inst(OpApp("AddCommGroup", W)),
            Inst(OpApp("Module", K, W)),
            All(Rho, OpApp("Representation", K, G, V),
                All(SigmaLower, OpApp("Representation", K, G, W), afterRepresentations)));
        return Disp(ForAll("K", TypeStar, ForAll("G", TypeStar, ForAll("V", TypeStar,
            ForAll("W", TypeStar, Seq(Inst(OpApp("RCLike", K)),
                GroupAndMeasure(K, representations)))))));
    }

    private static Formula SelfFormula()
    {
        Formula G = F.Id("G"), V = F.Id("V"), g = F.Id("g"), v = F.Id("v"), w = F.Id("w");
        Formula integrand = Mul(App(Phi, Act(Rho, g, v)), App(Psi, Act(Rho, Inverse(g), w)));
        Formula mass = OpApp("real", Mu, Op("univ"));
        Formula right = new Formula.Fraction(Mul(mass, Parenthesized(Mul(App(Phi, w), App(Psi, v)))),
            OpApp("finrank", Complexes, V));
        Formula conclusion = All(Phi, OpApp("Dual", Complexes, V), All(Psi, OpApp("Dual", Complexes, V),
            ForAll("v", V, ForAll("w", V, Equal(Integral(Mu, g, integrand), right)))));
        Formula afterMeasure = All(Rho, OpApp("Representation", Complexes, G, V), Seq(
            Inst(OpApp("IsIrreducible", Rho)),
            Implies(Parenthesized(ForAll("v", V, ContinuousIn(g, Act(Rho, g, v)))), conclusion)));
        return Disp(ForAll("G", TypeStar, ForAll("V", TypeStar, GroupAndMeasure(Complexes, afterMeasure))));
    }
}

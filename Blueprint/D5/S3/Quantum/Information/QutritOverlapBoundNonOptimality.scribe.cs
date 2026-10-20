using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class QutritOverlapBoundNonOptimalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/zozor2014entropylikeuncertainty");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Tsallis-two overlap bound is not attained by qutrit observables at interior overlaps.",
        H("The qutrit overlap entropy bound is unattainable"),
        Blocks(
            Paragraph(Text(
                "All indices range over Fin 3, and complex moduli and real parts have their usual meanings. "
                    + "The two probability maps read the diagonal in the standard basis and after conjugating a density matrix by T. "
                    + "The overlap parameter c is real.")),
            Node("tsallisTwo", "Tsallis entropy of order two", TsallisFormula(),
                "This is the Tsallis entropy for order two: h(x) = 1 − x and φ(x) = x², so the entropy is one minus the sum of squared probabilities.",
                AssessedProvenance.FromLiterature(Source)),
            Node("probA", "Standard-basis probabilities", ProbAFormula(),
                "For a complex 3 by 3 matrix ρ, the standard-basis probability p_i is the real part of its diagonal entry ρᵢᵢ.",
                AssessedProvenance.FromLiterature(Source)),
            Node("probB", "Transformed-basis probabilities", ProbBFormula(),
                "For a complex 3 by 3 matrix T and state ρ, the transformed probability q_j is the real part of the jth diagonal entry of TρT*, where T* is the conjugate transpose.",
                AssessedProvenance.FromLiterature(Source)),
            Node("boundD", "The source function D", BoundDFormula(),
                "The source function D uses h(x) = 1 − x and φ(x) = x². Its integer floor is the floor of 1 divided by cos²θ; the displayed expression is h applied to the two nonzero masses produced by that floor term.",
                AssessedProvenance.FromLiterature(Source)),
            Node("overlapBound", "The overlap bound", OverlapBoundFormula(),
                "The bound is the real infimum over θ in the closed interval from zero to arccos(c) of D(θ) plus D(arccos(c) − θ).",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Attainment by a qutrit density matrix", ClaimFormula(),
                "For every c strictly above 1/√2 and at most one, the claim asks for a unitary 3 by 3 matrix with all entry moduli at most c and one entry of modulus c, together with a positive semidefinite trace-one density matrix whose two Tsallis-two entropies attain the overlap bound.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("qutrit-overlap-bound-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Interior qutrit overlaps cannot attain the bound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For 1/√2 < c < 1, the floor in D is one throughout the interval, so D(θ) = (1 − cos(4θ))/4 and the infimum equals 1 − c², attained only at θ = arccos(c)/2.")),
                    Paragraph(Text(
                        "The entropy sum is concave in the density matrix because both probability maps are affine and Tsallis-two entropy is concave. It is therefore enough to consider a pure state, represented by a unit vector ψ; the density-matrix assertion reduces to the corresponding pair of measurement probability vectors for ψ.")),
                    Paragraph(Text(
                        "If the largest probability in either measurement is at most 1/2, its entropy is at least 1/2 and the desired strict comparison follows. Otherwise write the two largest probabilities as P = cos²θ and Q = cos²η. Cauchy–Schwarz on the components orthogonal to ψ gives |⟨a,b⟩| ≥ √(PQ) − √((1−P)(1−Q)) = cos(θ+η), so the entrywise overlap bound implies θ + η ≥ arccos(c). The entropy estimates then give S₂(p) + S₂(q) ≥ 1 − c².")),
                    Paragraph(Text(
                        "Equality would force ψ into the span of two standard-basis vectors and into the span of two transformed-basis vectors. Equality in Cauchy–Schwarz makes those two planes coincide. In dimension three their remaining basis vectors are both orthogonal to that plane, so their overlap has modulus one, contradicting c < 1.")),
                    Paragraph(Text(
                        "At c = 3/4 the bound is 1 − (3/4)² = 7/16. The universal attainment assertion would supply a state and unitary attaining this value, but the strict inequality above rules that out."))),
                DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("qutrit-overlap-bound-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Information", "QutritOverlapBoundNonOptimality", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Seq(Operatorname, Grp(F.Id(part))));
        }

        return Seq([.. items]);
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        At(Local(name), arguments);
    private static Formula QCall(string owner, string name, params Formula[] arguments) =>
        At(Qualified(owner, name), arguments);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Norm(Formula value) => new Formula.Norm(value);
    private static Formula SumOver(Formula variable, Formula body) =>
        Seq(new Formula.Subscript(Sum, variable), Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(F.Id(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin3() => At(Qualified("Fin"), D(3));
    private static Formula VectorReal() => new Formula.TypeArrow(Fin3(), RealType());
    private static Formula MatrixComplex() => At(Qualified("Matrix"), Fin3(), Fin3(), ComplexType());
    private static Formula MatrixEntry(Formula matrix, Formula row, Formula column) =>
        At(At(matrix, row), column);
    private static Formula RealPart(Formula value) => QCall("Complex", "re", value);

    private static Formula TsallisFormula()
    {
        Formula p = F.Id("p"), i = F.Id("i");
        return All("p", VectorReal(), Equal(Call("tsallisTwo", p),
            Subtract(D(1), SumOver(i, Power(At(p, i), D(2))))));
    }

    private static Formula ProbAFormula()
    {
        Formula rho = F.Id("rho"), i = F.Id("i");
        Formula rhs = Lambda("i", Fin3(), RealPart(MatrixEntry(rho, i, i)));
        return All("rho", MatrixComplex(), Equal(Call("probA", rho), rhs));
    }

    private static Formula ProbBFormula()
    {
        Formula t = F.Id("T"), rho = F.Id("rho"), j = F.Id("j");
        Formula transformed = Multiply(Multiply(t, rho), QCall("Matrix", "conjTranspose", t));
        Formula rhs = Lambda("j", Fin3(), RealPart(MatrixEntry(transformed, j, j)));
        return All("T", MatrixComplex(), All("rho", MatrixComplex(),
            Equal(Call("probB", t, rho), rhs)));
    }

    private static Formula BoundDFormula()
    {
        Formula theta = F.Id("theta"), cosine = QCall("Real", "cos", theta);
        Formula cosineSquared = Power(cosine, D(2));
        Formula floor = new Formula.Floor(Divide(D(1), cosineSquared));
        Formula remainder = Subtract(D(1), Multiply(floor, cosineSquared));
        Formula rhs = Subtract(D(1), Add(Multiply(floor, Power(cosineSquared, D(2))),
            Power(remainder, D(2))));
        return All("theta", RealType(), Equal(Call("boundD", theta), rhs));
    }

    private static Formula OverlapBoundFormula()
    {
        Formula c = F.Id("c"), theta = F.Id("theta");
        Formula gamma = QCall("Real", "arccos", c);
        Formula interval = QCall("Set", "Icc", D(0), gamma);
        Formula summand = Add(Call("boundD", theta), Call("boundD", Subtract(gamma, theta)));
        Formula image = QCall("Set", "image", Lambda("theta", RealType(), summand), interval);
        return All("c", RealType(), Equal(Call("overlapBound", c),
            At(Seq(Operatorname, Grp(F.Id("sInf"))), image)));
    }

    private static Formula ClaimFormula()
    {
        Formula c = F.Id("c"), t = F.Id("T"), rho = F.Id("rho");
        Formula i = F.Id("i"), j = F.Id("j");
        Formula lower = Less(Divide(D(1), Seq(Sqrt, Sp, Grp(D(2)))), c);
        Formula upper = LessEqual(c, D(1));
        Formula unitary = Member(t, At(Qualified("Matrix", "unitaryGroup"), Fin3(), ComplexType()));
        Formula entryBound = All("i", Fin3(), All("j", Fin3(),
            LessEqual(Norm(MatrixEntry(t, i, j)), c)));
        Formula attained = Some("i", Fin3(), Some("j", Fin3(),
            Equal(Norm(MatrixEntry(t, i, j)), c)));
        Formula density = And(QCall("Matrix", "PosSemidef", rho),
            And(Equal(QCall("Matrix", "trace", rho), D(1)),
                Equal(Add(Call("tsallisTwo", Call("probA", rho)),
                    Call("tsallisTwo", Call("probB", t, rho))),
                    Call("overlapBound", c))));
        return All("c", RealType(), Implies(lower, Implies(upper,
            Some("T", MatrixComplex(), And(unitary, And(entryBound,
                And(attained, Some("rho", MatrixComplex(), density))))))));
    }
}

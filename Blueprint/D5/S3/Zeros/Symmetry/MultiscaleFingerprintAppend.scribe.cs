using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class MultiscaleFingerprintAppendDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Zeros/Symmetry/MultiscaleFingerprintAppend.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite damping-defect history is stable under scale append, while an unequal new "
            + "defect separates extended fingerprints.",
        H("Multiscale Fingerprint Append"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-damping-defect-history"),
                DeclarationHandle.Create(Prefix + "multiscaleDampingFingerprint"),
                H("Finite damping-defect history"),
                StatementSource.FromAuthor(FingerprintDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each coordinate applies the frozen critical damping defect to the same "
                        + "finite carrier at one prescribed scale."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("appending-one-scale-preserves-and-separates"),
                DeclarationHandle.Create(Prefix + "multiscale_fingerprint_append"),
                H("Appending one scale preserves and separates"),
                StatementSource.FromAuthor(AppendTheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The snoc-castSucc law identifies every old coordinate with its extended "
                        + "counterpart. Equality of extended functions would also identify the "
                        + "last coordinates, contradicting unequal defects at the appended scale."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-scale-collision-separation"),
                DeclarationHandle.Create(Prefix + "two_scale_collision_separation"),
                H("The preregistered collision separates at scale two"),
                StatementSource.FromAuthor(PredictionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two-point centered offsets plus and minus one collide at scale one with "
                        + "the four-point offsets plus and minus b. The double-angle identity makes "
                        + "their scale-two difference the displayed strictly positive square."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/Symmetry/CriticalDampingFlatness")),
        ]));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula FingerprintDefinitionFormula()
    {
        Formula zero = F.Id("Zero");
        Formula n = F.Id("n");
        Formula realPart = F.Id("realPart");
        Formula scale = F.Id("scale");
        Formula k = F.Id("k");
        Formula real = Call("Real");
        Formula fingerprint = Apply(
            Call("multiscaleDampingFingerprint", realPart, scale),
            k);
        Formula defect = Call(
            "criticalDampingDefect",
            realPart,
            Apply(scale, k));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Zero", Call("Type")),
                Bound("n", Call("Nat")),
                Bound("realPart", Call("Function", zero, real)),
                Bound("scale", Call("Function", Call("Fin", n), real)),
                Bound("k", Call("Fin", n)),
            ],
            Implies(
                Call("Fintype", zero),
                Equal(fingerprint, defect))));
    }

    private static Formula AppendTheoremFormula()
    {
        Formula zero = F.Id("Zero");
        Formula zeroPrime = F.Id("ZeroPrime");
        Formula n = F.Id("n");
        Formula realPart = F.Id("realPart");
        Formula realPartPrime = F.Id("realPartPrime");
        Formula scale = F.Id("scale");
        Formula tauNew = F.Id("tauNew");
        Formula k = F.Id("k");
        Formula real = Call("Real");
        Formula extendedScale = Call("snoc", scale, tauNew);
        Formula oldCoordinate = Apply(
            Call("multiscaleDampingFingerprint", realPart, scale),
            k);
        Formula extendedCoordinate = Apply(
            Call("multiscaleDampingFingerprint", realPart, extendedScale),
            Call("castSucc", k));
        Formula prefix = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("k", Call("Fin", n))],
            Equal(extendedCoordinate, oldCoordinate));
        Formula newDefectsDiffer = NotEqual(
            Call("criticalDampingDefect", realPart, tauNew),
            Call("criticalDampingDefect", realPartPrime, tauNew));
        Formula extendedFingerprintsDiffer = NotEqual(
            Call("multiscaleDampingFingerprint", realPart, extendedScale),
            Call("multiscaleDampingFingerprint", realPartPrime, extendedScale));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Zero", Call("Type")),
                Bound("ZeroPrime", Call("Type")),
                Bound("n", Call("Nat")),
                Bound("realPart", Call("Function", zero, real)),
                Bound("realPartPrime", Call("Function", zeroPrime, real)),
                Bound("scale", Call("Function", Call("Fin", n), real)),
                Bound("tauNew", real),
            ],
            Implies(
                And(Call("Fintype", zero), Call("Fintype", zeroPrime)),
                And(prefix, Implies(newDefectsDiffer, extendedFingerprintsDiffer)))));
    }

    private static Formula PredictionFormula()
    {
        Formula one = D(1);
        Formula two = D(2);
        Formula half = new Formula.Fraction(one, two);
        Formula b = F.Id("b");
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula coshOne = Call("cosh", one);
        Formula bValue = Call(
            "arcosh",
            new Formula.Fraction(Add(coshOne, one), two));
        Formula xValue = Call(
            "Vector",
            new Formula.Fraction(D(3), two),
            new Formula.Negate(half));
        Formula yValue = Call(
            "Vector",
            Add(half, b),
            Add(half, b),
            Subtract(half, b),
            Subtract(half, b));
        Formula firstDefectX = Call("criticalDampingDefect", x, one);
        Formula firstDefectY = Call("criticalDampingDefect", y, one);
        Formula secondDefectX = Call("criticalDampingDefect", x, two);
        Formula secondDefectY = Call("criticalDampingDefect", y, two);
        Formula commonValue = Multiply(two, Subtract(coshOne, one));
        Formula positiveSquare = Multiply(
            two,
            new Formula.Power(Subtract(coshOne, one), two));
        Formula body = And(
            Equal(firstDefectX, firstDefectY),
            And(
                Equal(firstDefectX, commonValue),
                And(
                    Equal(firstDefectY, commonValue),
                    And(
                        Equal(Subtract(secondDefectX, secondDefectY), positiveSquare),
                        And(
                            LessThan(D(0), positiveSquare),
                            NotEqual(secondDefectX, secondDefectY))))));

        return Disp(Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            b, Sp, Colon, Eq, Sp, bValue, SemiSpace,
            Operatorname, Grp(F.Id("let")), Sp,
            x, Sp, Colon, Eq, Sp, xValue, SemiSpace,
            Operatorname, Grp(F.Id("let")), Sp,
            y, Sp, Colon, Eq, Sp, yValue, SemiSpace,
            body));
    }
}

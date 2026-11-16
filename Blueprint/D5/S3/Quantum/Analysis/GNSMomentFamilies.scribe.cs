using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class GNSMomentFamiliesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/GNSMomentFamilies.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full complex continuous moments and the actual completed GNS commutant.",
        H("Continuous moments in the GNS commutant"),
        Blocks(
            Paragraph(Text("Let A be an arbitrary unital complex C-star algebra with its compatible star order, and let rho and sigma be positive continuous complex-linear functionals. Put psi=rho+sigma. All operators below act on Mathlib's actual completed GNS Hilbert space of psi. Omega is the image of the unit, with no normalization. The commutant N is the norm-closed star subalgebra of operators commuting with the actual GNS representation of every a in A. The construction includes zero and singular input functionals and nonseparable Hilbert spaces. It does not require normality of the GNS representation.")),
            Definition("commutant", "The actual closed operator commutant",
                "N is the star-subalgebra centralizer of the range of the completed GNS representation. Because that range is star closed, membership is exactly commutation with every represented element. Its carrier is closed, so N inherits the C-star norm, completeness and the usual operator order."),
            Definition("coefficientMap", "An injective complex-linear coefficient map",
                "For T in N define K(T)(a)=<Omega,T pi(a) Omega>. This is the existing continuous coefficient functional, now assembled as a complex-linear map from the actual commutant into the continuous dual of A. Its linearity follows from linearity of the inner product in the second argument."),
            Theorem("coefficientMap_injective", "Coefficients determine commutant operators",
                "Equality K(T)=K(S) implies T=S, by the cyclic coefficient injectivity theorem. Both operators may be arbitrary complex commutant operators; positivity is unnecessary."),
            Theorem("coefficientMap_nonneg", "The coefficient reflects positivity",
                "K(T) is nonnegative on every positive a in A if and only if T is positive in N. This is the positive coefficient reflection theorem for the actual dense cyclic orbit, with the inherited operator order."),
            Theorem("coefficientMap_order", "Coefficient order is exactly operator order",
                "For arbitrary commutant operators T and S, K(T)(a)<=K(S)(a) on every positive a if and only if T<=S. This directly reuses the existing cyclic GNS order-reflection theorem and supplies both original overlap feasibility bounds."),
            Theorem("coefficientMap_one", "The unit has its original GNS coefficient",
                "The coefficient of the identity is precisely psi. Evaluating at a gives the GNS inner product of the images of 1 and a, which equals psi(a), including when the GNS space is zero."),
            Definition("vectorFunctional", "The actual unnormalized vector functional",
                "Define phi(T)=K(T)(1)=<Omega,T Omega>. This is a positive complex-linear functional on N."),
            Theorem("vectorFunctional_faithful", "Faithfulness on positive commutant operators",
                "If T is positive in N and phi(T)=0, then T=0. Indeed K(T) is a positive continuous functional on A. Its norm equals its real mass at the unit, hence it has norm zero. Injectivity of K then forces T=0. This proves positivity-faithfulness of the actual GNS vector functional on N without assuming faithfulness of psi on A."),
            Definition("pairFunctional", "The original positive GNS input",
                "Convert the original continuous dual functional rho+sigma to a positive complex-linear map without changing any value."),
            Definition("pairCoordinate", "The original first-moment operator",
                "Use rho<=psi to construct the GNS comparison contraction J, and set C=J*J in N. Thus 0<=C<=I, K(C)=rho and K(I-C)=sigma. No coordinate operator is supplied as a premise."),
            Theorem("pairCoordinate_coefficient", "Exact first-moment coefficient",
                "The constructed C has coefficient rho on every complex input a in A, by the dominated GNS coordinate formula."),
            Theorem("exists_lift", "Every full Family has an actual positive lift",
                "For an actual NormalMomentFamily.Family F, let J_F be its complex-linear map on all complex continuous functions on [0,1]. A nonnegative g obeys 0<=J_F(g)<=(norm(g)+1) psi on positive algebra elements. Apply the dominated GNS coordinate theorem to J_F(g)/(norm(g)+1), then scale its coordinate, to put J_F(g) in the range of K. The C-star four-positive-part decomposition puts every J_F(g) in this same complex-linear range. Invert the injective linear coefficient map on its range and compose with J_F. The resulting actual positive complex-linear Z takes values in N, satisfies Z(1)=I and Z(u)=C, and K(Z(g))=J_F(g) for every complex continuous g. No norm-dependent choice is assumed linear; linearity comes from the range equivalence."),
            Definition("familyOfMap", "The converse with the prescribed first moment",
                "For a positive complex-linear Z into N with Z(1)=I and Z(u)=C, compose K with Z and apply NormalMomentFamily.ofLinearMap. This constructs the full Family for the fixed original pair. The first-moment condition is essential: a positive unital map with another value at u describes another pair."),
            Theorem("familyOfMap_agrees", "Every complex coordinate is retained",
                "The Family constructed from Z has J_F(g)=K(Z(g)) for every complex continuous g, by the actual definition of its continuous dual coordinates."),
            Definition("familyEquiv", "The full correspondence",
                "There is an actual equivalence between the full Family for rho and sigma and positive complex-linear maps Z into N with Z(1)=I and Z(u)=C. The forward and reverse constructions are inverse on every complex continuous function. Equality on the operator side follows from coefficient injectivity, while equality on the Family side is equality of all continuous dual coordinates."),
            Paragraph(Text("These are classical GNS order and positive-map constructions. The domain is the whole complex continuous-function algebra, not a polynomial or simple-function restriction. Positive maps between the inherited ordered C-star algebras are automatically bounded. The correspondence alone asserts neither normality of the original GNS representation nor a compressed-centralizer classification."))
        )));

    private static DocumentBlock Theorem(string name, string heading, string prose) =>
        Describe.Lean(DescribeId.Create("gns-moments-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string name, string heading, string prose) =>
        Describe.Lean(DescribeId.Create("gns-moments-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}

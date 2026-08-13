using Dunet;

namespace StrataLint.Engine;

[Union(EnableImplicitConversions = false)]
public partial record ValidationProfile
{
    public partial record StructuredJson();

    public partial record StructuredYaml();

    public partial record LeanModule();

    public partial record OpaqueText();
}

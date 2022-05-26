
import re

r'''
    TESTS:

        sage: version_ok(version())
        True

'''


def version_ok(ver):
    r'''

    TESTS:
        sage: version_ok('SageMath version 9.6')
        True
        sage: version_ok('SageMath version 9.5.10')
        False
        sage: version_ok('SageMath version 9')
        Traceback (most recent call last):
        ...
        RuntimeError: Unrecognized version string: "SageMath version 9"    
    '''
    m = re.match(r'SageMath version ([0-9]+)\.([0-9]+)', ver)
    if not m or len(m.groups()) != 2:
        raise RuntimeError(f'Unrecognized version string: "{ver}"')
    major = int(m.groups()[0])
    minor = int(m.groups()[1])
    return (major > 9) or (major == 9 and minor >= 6)


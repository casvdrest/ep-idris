module TSS.Shell

import Logic

%access public export

-- Embedding of the "cat" command: read the contents of a file and
-- output to the command line. (This is obviously not what cat actually does,
-- but we'll pretend it does anyway)
syntax cat file =
  -- cat "file" is only possible if "file" exists,
  -- "file" does not refer to a directory, and
  -- the current user has read access on "file"
  {{ (exists file) /\
     (isFile file) /\
     (accessRead file)
  }}-
    id
  -{{ const True }}

-- Embedding of the "ls" command: read the contents of a directory and
-- write to std out.
syntax ls [path] =
  -- A directory listing can only be done if the directory actually exists,
  -- the path refers to a directory, and the current user has read access
  -- to that directory.
  {{ (exists path)      /\
     (isDirectory path) /\
     (accesRead path)
  }}-
    id
  -{{ const True }}

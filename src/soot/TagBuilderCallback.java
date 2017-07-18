package soot;

import soot.tagkit.AnnotationTag;
import soot.tagkit.Host;

/**
 * Created by adann on 05.05.17.
 */
public interface TagBuilderCallback {


    public void tagBuild(Host host , AnnotationTag annotationTag);
}
